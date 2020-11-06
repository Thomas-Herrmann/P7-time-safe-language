module Partition
    ( Partition.partition
    ) where

import Data.Set as Set
import Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.State as State
import Data.Foldable
import Ast


type ParT a = MaybeT (State Integer) a


partition :: Exp -> Integer -> Maybe (Set Val, Integer)
partition e n = 
    case runState (runMaybeT (partitionExp e)) n of
        (Nothing, _)  -> Nothing
        (Just set, s) -> Just (set, s)


next :: ParT Integer
next = State.get >>= (\n -> State.put (n + 1) >> (return n))


partitionExp :: Exp -> ParT (Set Val)
partitionExp (ValExp v) = return $ Set.singleton v
partitionExp (RefExp _) = return Set.empty
partitionExp (FixExp (ValExp (MatchVal body@(SingleMatch (RefPat _) _)))) = return $ Set.singleton (MatchVal body)
partitionExp (GuardExp e _)   = partitionExp e
partitionExp (LetExp x e1 e2) = partitionExp e1 >>= (\set -> foldrM fun Set.empty set)
    where
        fun v set = (partitionExp . (substitute e2)) (Map.singleton x v) >>= (\set' -> return (set `Set.union` set'))

partitionExp (SyncExp body) = partitionBody body
    where
        partitionBody :: SyncBody -> ParT (Set Val)
        partitionBody (SingleSync (ReceiveSync _ y) e)    = partitionExp $ substitute e (Map.singleton y (TermVal "Nil" []))
        partitionBody (SingleSync _ e)                    = partitionExp e
        partitionBody (MultiSync (ReceiveSync _ y) e rem) = do
            set  <- partitionExp (substitute e (Map.singleton y (TermVal "Nil" [])))
            set' <- partitionBody rem
            return $ set `Set.union` set'

        partitionBody (MultiSync _ e rem) = do 
            set  <- partitionExp e
            set' <- partitionBody rem
            return $ set `Set.union` set'

partitionExp (ParExp e1 e2) = do
    set1 <- partitionExp e1
    set2 <- partitionExp e2
    return $ Set.fromList [TermVal "Pair" [v1, v2] | v1 <- Set.toList set1, v2 <- Set.toList set2]

partitionExp (InvarExp _ _ _ e1 e2) = do
    set1 <- partitionExp e1
    set2 <- partitionExp e2
    return $ set1 `Set.union` set2

partitionExp (AppExp e1 e2) = partitionExp e1 >>= (\set -> foldrM unionApply Set.empty set)
    where
        unionApply v set       = apply v e2 >>= (\set' -> return (set `Set.union` set')) 
        unionMatch body v set  = matchBody body v >>= (\set' -> return (set `Set.union` set'))
        unionPartition e v set = partitionExp e >>= (\set' -> return (set `Set.union` set'))

        apply :: Val -> Exp -> ParT (Set Val)
        apply (MatchVal body) e2   = partitionExp e2 >>= (\set -> foldrM (unionMatch body) Set.empty set)
        apply (TermVal x vs) e2    = partitionExp e2 >>= (\set -> return (Set.fromList [TermVal x (vs ++ [v]) | v <- Set.toList set]))
        apply (ConVal ResetCon) e2 = partitionExp e2
        apply (ConVal OpenCon) e2  = do 
            id  <- next
            set <- partitionExp e2
            return $ Set.map (\v -> TermVal "Triple" [SendVal id, ReceiveVal id, v]) set

        matchBody :: MatchBody -> Val -> ParT (Set Val)
        matchBody (SingleMatch p e) v    = partitionExp $ substitute e (match p v)
        matchBody (MultiMatch p e rem) v = do 
            set  <- partitionExp $ substitute e (match p v) 
            set' <- matchBody rem v
            return $ set `Set.union` set'

partitionExp _ = mzero


match :: Pat -> Val -> Subst
match (RefPat x) v                  = Map.singleton x v
match (TermPat _ ps) (TermVal _ vs) = Prelude.foldr (\(p, v) -> (\sigma -> sigma `Map.union` match p v)) Map.empty $ Prelude.zip ps vs