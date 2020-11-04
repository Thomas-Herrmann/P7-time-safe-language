module Translate
    ( 
    ) where

import Data.Set as Set
import Data.Map as Map
import Ast


partitionExp :: Exp -> Set Val
partitionExp (ValExp v) = Set.singleton v
partitionExp (RefExp _) = Set.empty
partitionExp (FixExp (ValExp (MatchVal body@(SingleMatch (RefPat _) _)))) = Set.singleton $ MatchVal body
partitionExp (GuardExp e _)   = partitionExp e
partitionExp (LetExp x e1 e2) = Set.fold (Set.union . partitionExp . (substitute e2) . (Map.singleton x)) Set.empty $ partitionExp e1
partitionExp (SyncExp body)   = partitionBody body
    where
        partitionBody (SingleSync (ReceiveSync _ y) e)    = partitionExp $ substitute e (Map.singleton y (TermVal "Nil" []))
        partitionBody (SingleSync _ e)                    = partitionExp e
        partitionBody (MultiSync (ReceiveSync _ y) e rem) = partitionExp (substitute e (Map.singleton y (TermVal "Nil" []))) `Set.union` partitionBody rem
        partitionBody (MultiSync _ e rem)                 = partitionExp e `Set.union` partitionBody rem

partitionExp (ParExp e1 e2)         = Set.fromList [TermVal "Pair" [v1, v2] | v1 <- Set.toList (partitionExp e1), v2 <- Set.toList (partitionExp e2)]
partitionExp (InvarExp _ _ _ e1 e2) = partitionExp e1 `Set.union` partitionExp e2
partitionExp (AppExp e1 e2)         = Set.fold (\v -> (\set -> set `Set.union` apply v e2)) Set.empty $ partitionExp e1
    where
        apply :: Val -> Exp -> Set Val
        apply (MatchVal body) e2   = Set.fold (\v -> (\set -> set `Set.union` matchBody body v)) Set.empty $ partitionExp e2
        apply (TermVal x vs) e2    = Set.fromList [TermVal x (vs ++ [v]) | v <- Set.toList (partitionExp e2)]
        apply (ConVal ResetCon) e2 = partitionExp e2
        apply (ConVal OpenCon) e2  = Set.map (\v -> TermVal "Triple" [SendVal 1, ReceiveVal 1, v]) $ partitionExp e2 -- TODO: not 1, but new value (wrap in monad)

        matchBody :: MatchBody -> Val -> Set Val
        matchBody (SingleMatch p e) v    = Prelude.foldr (Set.union . partitionExp) Set.empty [substitute e sigma | sigma <- Set.toList (match p (ValExp v))]
        matchBody (MultiMatch p e rem) v = Prelude.foldr (Set.union . partitionExp) Set.empty [substitute e sigma | sigma <- Set.toList (match p (ValExp v))] `Set.union` matchBody rem v


match :: Pat -> Exp -> Set Subst
match (RefPat x) e     = Set.fromList [Map.singleton x v | v <- Set.toList (partitionExp e)]
match (TermPat _ ps) e = setbuilder $ Set.toList $ partitionExp e
    where
        substbuilder :: [Pat] -> [Val] -> [Set Subst]
        substbuilder [] []         = []
        substbuilder (p:ps) (v:vs) = (match p (ValExp v)):(substbuilder ps vs)

        combinations :: [Set Subst] -> [Subst] -> [Subst]
        combinations [] substs         = substs
        combinations (set:sets) substs = combinations sets substs'
            where
                substs' = Set.fold (\sigma -> (\l -> l ++ (Prelude.map (Map.union sigma) substs))) [] set

        setbuilder :: [Val] -> Set Subst
        setbuilder []                                            = Set.empty
        setbuilder ((TermVal _ vs):rem) | length vs == length ps = Set.fromList (combinations (substbuilder ps vs) [Map.empty]) `Set.union` setbuilder rem
        setbuilder (_:rem)                                       = setbuilder rem
