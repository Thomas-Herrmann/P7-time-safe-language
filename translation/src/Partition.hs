module Partition
    ( Partition.partition
    , match
    , sends
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
partitionExp (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) e)))) = partitionExp e
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
        matchBody (SingleMatch p e) v =
            case match p v of
                Nothing    -> return Set.empty
                Just sigma -> partitionExp $ substitute e sigma
        matchBody (MultiMatch p e rem) v =
            case match p v of
                Nothing    -> matchBody rem v
                Just sigma -> do
                    set  <- partitionExp $ substitute e sigma
                    set' <- matchBody rem v
                    return $ set `Set.union` set'

partitionExp _ = mzero


match :: Pat -> Val -> Maybe Subst
match (RefPat x) v                                           = Just $ Map.singleton x v
match (TermPat name1 ps) (TermVal name2 vs) | name1 == name2 = Prelude.foldr accumulator (Just Map.empty) $ Prelude.zip ps vs
    where
        accumulator _ Nothing           = Nothing
        accumulator (p, v) (Just sigma) =
            case match p v of 
                Nothing     -> Nothing 
                Just sigma' -> Just $ sigma `Map.union` sigma'

match _ _ = Nothing

sends :: Exp -> Integer -> Maybe (Map Integer (Set Val), Integer)
sends e n = 
    case runState (runMaybeT (sendsExp e)) n of
        (Nothing, _)  -> Nothing
        (Just set, s) -> Just (set, s)

sendsExp ::  Exp -> ParT (Map Integer (Set Val))
sendsExp (ValExp _)     = return Map.empty
sendsExp (AppExp e1 e2) = do 
    map1 <- sendsExp e1 
    map2 <- sendsExp e2
    vs1  <- partitionExp e1
    vs2  <- partitionExp e2
    map3 <- applySends (Set.toList vs1) (Set.toList vs2)
    return $ (Map.unionWith Set.union) ((Map.unionWith Set.union) map1 map2) map3
    where
        getExps (MatchVal body) v2 = matchBody body v2
        getExps _ _                = Set.empty

        matchBody (SingleMatch p e) v =
            case match p v of
                Nothing    -> Set.empty
                Just sigma -> Set.singleton $ substitute e sigma

        matchBody (MultiMatch p e rem) v = 
            case match p v of
                Nothing    -> matchBody rem v
                Just sigma -> Set.singleton (substitute e sigma) `Set.union` matchBody rem v

        applySends vs1 vs2 = do
            let es = Prelude.foldr Set.union Set.empty [getExps v1 v2 | v1 <- vs1, v2 <- vs2]
            maps   <- Prelude.sequence $ Prelude.map sendsExp $ Set.toList es
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty maps

    
sendsExp (FixExp (ValExp (MatchVal body@(SingleMatch (RefPat _) _)))) = return Map.empty

sendsExp (InvarExp _ xs _ e1 e2) = do 
    map1 <- sendsExp e1
    map2 <- sendsExp e2 
    return $ (Map.unionWith Set.union) map1 map2 -- TODO: substitute in e2 (xs (maybe..))

sendsExp (LetExp x e1 e2) = do 
    map1    <- sendsExp e1
    vs1     <- partitionExp e1
    mapList <- Prelude.sequence [sendsExp (substitute e2 (Map.singleton x v)) | v <- Set.toList vs1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

sendsExp (SyncExp body) = return $ sendsBody body -- TODO: multiple passes!
    where
        sendsBody :: SyncBody -> Map Integer (Set Val)
        sendsBody (SingleSync (SendSync (Right (SendVal id)) x (Just v)) e)    = Map.singleton id $ Set.singleton v 
        sendsBody (MultiSync (SendSync (Right (SendVal id)) x (Just v)) e rem) = (Map.unionWith Set.union) (Map.singleton id (Set.singleton v)) (sendsBody rem)
        sendsBody (MultiSync q e rem)                           = sendsBody rem
        sendsBody _                                             = Map.empty


sendsExp (GuardExp e _) = sendsExp e

sendsExp (ParExp e1 e2) = do 
    map1 <- sendsExp e1 
    map2 <- sendsExp e2
    return $ (Map.unionWith Set.union) map1 map2


