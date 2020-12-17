module Partition
    ( Partition.partition
    , match
    , sends
    , multiPassSends
    , snapshots
    ) where

import Data.Set as Set(Set, empty, fromList, null, singleton, toList, union)
import Data.Map as Map(Map, (!), empty, foldrWithKey, insert, mapWithKey, member, singleton, union, unionWith)
import Control.Monad.State as State
import Data.Functor((<&>))
import Data.Foldable
import Ast


-- Implementation of the partition function.
-- Tries to find a set of possible values that the specified expression may reduce to,
-- given the specified possible values to be received.
-- The function fails for some invalid expressions.
-- The function does not find the complete set of possible values,
-- if it cannot be computed by recursively traversing recursive functions exactly once.
-- For instance, a recursive function that applies a new value to a termconstructor indefinitely cannot be computed this way.
-- However, this is only a problem, if a match function in either the specified expression, or at the usage of the returned set,
-- has a pattern that can only be matched after more than one simulated recursion.
partition :: Map Integer (Set Val) -> Exp -> Maybe (Set Val)
partition _ (ValExp v) = return $ Set.singleton v
partition _ (RefExp _) = return Set.empty
partition _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat x) (ValExp (MatchVal body)))))) = return $ Set.singleton (RecMatchVal x body)
partition receivables (GuardExp e _) = partition receivables e
-- The possible values are the possible values of all variants of e2 with 'x' substituted for some value in partition(e1)
partition receivables (LetExp x e1 e2) = partition receivables e1 >>= foldrM fun Set.empty
    where
        fun v set = (partition receivables . substitute e2) (Map.singleton x v) <&> Set.union set

-- The possible values are the possible values of all the synchronization branches.
-- If the synchronization is to receive on a channel,
-- we substitute for values in the 'receivables' set for the channel.
partition receivables (SyncExp body) = partitionBody body
    where
        partitionBody :: SyncBody -> Maybe (Set Val)
        partitionBody (SingleSync q e)    = partitionSync q e
        partitionBody (MultiSync q e rem) = do
            set  <- partitionSync q e
            set' <- partitionBody rem
            return $ set `Set.union` set'

        partitionSync :: Sync -> Exp -> Maybe (Set Val)
        -- We have a binding in 'receivables' for the channel to be received on,
        -- recursively call partition on 'e' with 'x' substituted for each possible value to be received.
        partitionSync (ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            setList <- Prelude.sequence [partition receivables (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            return $ Prelude.foldr Set.union Set.empty setList

        -- It is not possible to receive a value on the channel, so the empty set is returned
        partitionSync (ReceiveSync (Right (ReceiveVal _)) _) _    = return Set.empty
        partitionSync (SendSync (Right (SendVal _)) _ (Just _)) e = partition receivables e
        partitionSync (GetSync (Right (InPinVal _)) _) e          = partition receivables e
        partitionSync (SetSync (Right (OutPinVal _)) _) e         = partition receivables e

        partitionSync _ _ = mzero

-- As a parallel composition reduces to a 'Pair' term,
-- we call partition on the two subexpressions and return all possible pairs.
partition receivables (ParExp e1 e2) = do
    set1 <- partition receivables e1
    set2 <- partition receivables e2
    return $ Set.fromList [TermVal "Pair" [v1, v2] | v1 <- Set.toList set1, v2 <- Set.toList set2]

-- For invariants, the possible values are found by recursively calling partition on e1 and e2.
-- However, for e2 the values may depend on how much e1 was reduced before failure.
-- Thus, we use the snapshots function on e1 to find all the possible substitutions,
-- representing the progress in e1 upon timeout.
partition receivables (InvarExp _ _ subst e1 e2) = do
    set1    <- partition receivables e1
    sigmas  <- snapshots receivables subst e1
    let e2' = substitute e2 subst -- TODO: verify that this is right?
    setList <- Prelude.sequence [partition receivables (substitute e2' sigma) | sigma <- Set.toList sigmas]
    return $ Prelude.foldr Set.union set1 setList

-- For function application, we recursively call partition on e1 and e2.
-- We require that all possible values of e1 are of function type.
-- The possible values then depend on the function types.
partition receivables (AppExp e1 e2) = partition receivables e1 >>= foldrM unionApply Set.empty
    where
        unionApply v set       = apply v <&> Set.union set
        unionMatch body        = partition receivables e2 >>= matchBody body

        apply :: Val -> Maybe (Set Val)
        apply (MatchVal body)      = unionMatch body
        apply (RecMatchVal x body) = unionMatch $ substitute body (Map.singleton x (MatchVal body)) -- Perform recursion once to hopefully find all value patterns
        apply (TermVal x vs)       = partition receivables e2 >>= (\set -> return (Set.fromList [TermVal x (vs ++ [v]) | v <- Set.toList set]))
        apply (ConVal ResetCon)    = partition receivables e2
        apply _                    = mzero

        matchSet :: Pat -> Exp -> Set Val -> Maybe (Set Val)
        matchSet p e set = foldrM (\v set' -> matchf v <&> Set.union set') Set.empty $ Set.toList set
            where
                    matchf v =    
                        case match p v of
                            Nothing    -> return Set.empty
                            Just sigma -> partition receivables $ substitute e sigma

        matchBody :: MatchBody -> Set Val -> Maybe (Set Val)
        matchBody (SingleMatch p e) set = do 
            set' <- matchSet p e set
            when (Set.null set') mzero
            return set'

        matchBody (MultiMatch p e rem) set = do 
            set' <- matchSet p e set 
            when (Set.null set') mzero
            matchBody rem set <&> Set.union set'

-- None of the valid patterns were matched, fail.
partition _ _ = mzero


-- Implementation of the match function.
-- Tries to match the specified pattern and value.
-- Upon success, a substitution "partitioning" the value over the pattern variables is returned.
match :: Pat -> Val -> Maybe Subst
match (RefPat x) v                                                                     = Just $ Map.singleton x v
match (TermPat x ps) (TermVal y vs) | x == y && Prelude.length ps == Prelude.length vs = Prelude.foldr accumulator (Just Map.empty) $ Prelude.zip ps vs
    where
        accumulator _ Nothing           = Nothing
        accumulator (p, v) (Just sigma) =
            case match p v of 
                Nothing     -> Nothing 
                Just sigma' -> Just $ sigma `Map.union` sigma'

match _ _ = Nothing


-- Implementation of the snapshots function.
-- Tries to find the set of possible substitutions of the specified expression,
-- representing the steps in its reduction sequence.
-- The specified substitution contains the variables we are interested in,
-- as well as their default value (before reduction of the expression).
-- The function overapproximates in that it returns all substitutions,
-- constructable using the cartesian product on the set of possible values for each variable,
-- whereas it is often the case that reduction of the expression affects variables in a clear order.
snapshots :: Map Integer (Set Val) -> Subst -> Exp -> Maybe (Set Subst)
-- snapshotsAux returns a map from variables to sets of possible values,
-- we construct the substitutions based on the cartesian product of the set for each value.
snapshots receivables subst e = do
    possibilityMap <- snapshotsAux receivables e
    return $ cartesianProduct $ Map.mapWithKey addDefault possibilityMap
    where
        cartesianProduct :: Map Name (Set Val) -> Set Subst
        cartesianProduct possibilityMap = Map.foldrWithKey addBindings (Set.singleton Map.empty) possibilityMap

        addBindings x vs sigmas = Set.fromList [Map.insert x v sigma | v <- Set.toList vs, sigma <- Set.toList sigmas]

        addDefault x vs | x `Map.member` subst = vs `Set.union` Set.fromList [TermVal "Nothing" [], subst ! x]
                        | otherwise            = vs `Set.union` Set.singleton (TermVal "Nothing" [])


-- Implementation of the auxiliary function for snapshot.
-- Returns a map from variables to sets of possible values of these variables.
-- We are only interested in synchronizations here.
snapshotsAux :: Map Integer (Set Val) -> Exp -> Maybe (Map Name (Set Val))
snapshotsAux _ (ValExp _) = return Map.empty
snapshotsAux _ (RefExp _) = return Map.empty

-- Synchronizations may appear in e1, e2 or in any of the resulting function bodies in a function application.
-- Thus, we recursively call snapshotsAux on e1 and e2, and use the partition function to find the possible applied function bodies,
-- on which we call snapShotsAux recursively.
snapshotsAux receivables (AppExp e1 e2) = do
    map1 <- snapshotsAux receivables e1
    map2 <- snapshotsAux receivables e2
    vs1  <- partition receivables e1
    vs2  <- partition receivables e2
    map3 <- applySnapshots (Set.toList vs1) (Set.toList vs2)
    return $ Map.unionWith Set.union (Map.unionWith Set.union map1 map2) map3
    where
        -- We are only interested in functions with bodies
        getExps (MatchVal body) v2      = matchBody body v2
        getExps (RecMatchVal x body) v2 = matchBody (substitute body (Map.singleton x (MatchVal body))) v2
        getExps _ _                     = Set.empty

        matchBody (SingleMatch p e) v =
            case match p v of
                Nothing    -> Set.empty
                Just sigma -> Set.singleton $ substitute e sigma

        matchBody (MultiMatch p e rem) v = 
            case match p v of
                Nothing    -> matchBody rem v
                Just sigma -> Set.singleton (substitute e sigma) `Set.union` matchBody rem v

        applySnapshots :: [Val] -> [Val] -> Maybe (Map Name (Set Val))
        applySnapshots vs1 vs2 = do
            let es = Prelude.foldr Set.union Set.empty [getExps v1 v2 | v1 <- vs1, v2 <- vs2]
            maps   <- Prelude.mapM (snapshotsAux receivables) $ Set.toList es
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty maps


snapshotsAux _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = return Map.empty

-- For invariants, we first call snapshotsAux recursively on e1.
-- We then must call snapshots on e1,
-- to find the possible variants of e2, on which we recursively call snapshotsAux,
-- as there may be synchronizations in these.
snapshotsAux receivables (InvarExp _ _ subst e1 e2) = do
    map1    <- snapshotsAux receivables e1
    set1    <- snapshots receivables subst e1
    mapList <- Prelude.sequence [snapshotsAux receivables (substitute e2 sigma) | sigma <- Set.toList set1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

-- Let expressions are similar to invariants,
-- expect we call partition rather than snapshots,
-- as we must find the possible values of 'x' to construct the variants of e2.
snapshotsAux receivables (LetExp x e1 e2) = do
    map1    <- snapshotsAux receivables e1
    vs1     <- partition receivables e1
    mapList <- Prelude.sequence [snapshotsAux receivables (substitute e2 (Map.singleton x v)) | v <- Set.toList vs1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

-- For synchronization expressions, we are interested in receiving synchronizations and the branch expressions.
-- We construct a singleton map for each receiving synchronization, 
-- based on the possible values that may be received on the corresponding channel.
-- We recursively call snapshotsAux on the synchronization branches.
snapshotsAux receivables (SyncExp body) = snapshotsBody body
    where
        snapshotsBody (SingleSync q e)    = snapshotsSync q e
        snapshotsBody (MultiSync q e rem) = do 
            map1 <- snapshotsSync  q e
            map2 <- snapshotsBody rem
            return $ Map.unionWith Set.union map1 map2

        -- It is possible to receive a value on the channel, build a singleton map, corresponding to the values
        snapshotsSync (ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            let map1 = Map.singleton x $ receivables ! id
            mapList <- Prelude.sequence [snapshotsAux receivables (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

        -- It is not possible to receive a value on the channel, return the empty map
        snapshotsSync (ReceiveSync (Right (ReceiveVal _)) _) _ = return Map.empty
        snapshotsSync (ReceiveSync _ _) _                      = mzero

        snapshotsSync _ e = snapshotsAux receivables e

snapshotsAux receivables (GuardExp e _) = snapshotsAux receivables e

-- There may be synchronization expressions in either e1 or e2,
-- so we recursively call snapshotsAux on them.
snapshotsAux receivables (ParExp e1 e2) = do
    map1 <- snapshotsAux receivables e1
    map2 <- snapshotsAux receivables e2
    return $ Map.unionWith Set.union map1 map2

-- None of the valid patterns were matched, fail
snapshotsAux _ _ = mzero


-- Function that iteratively applies the sends function to the two specified expressions.
-- The specified integer determines the number of iterations.
-- Each iteration, the previous maps are specified as the new receivables.
-- Thus, the function simulates possible iterative synchronizations between two expressions in a parallel composition.
multiPassSends :: Exp -> Exp -> Integer -> Maybe (Map Integer (Set Val), Map Integer (Set Val))
multiPassSends e1 e2 = multiPassAux Map.empty Map.empty
    where
        multiPassAux :: Map Integer (Set Val) -> Map Integer (Set Val) -> Integer -> Maybe (Map Integer (Set Val), Map Integer (Set Val))
        multiPassAux receivables1 receivables2 n | n <= 1    = return (receivables2, receivables1)
                                                 | otherwise = do
            map1 <- sends receivables1 e1
            map2 <- sends receivables2 e2
            multiPassAux map2 map1 $ n - 1


-- Implementation of the sends function, 
-- tries to find a map from channel identifiers to sets of possible values to be sent/received.
sends :: Map Integer (Set Val) -> Exp -> Maybe (Map Integer (Set Val))
sends _ (ValExp _)               = return Map.empty
sends _ (RefExp _)               = return Map.empty

-- In a function application, we may synchronize in e1, e2 or any function body.
-- Thus, we apply sends recursively on these.
-- We use the partition function to find the possible function bodies.
sends receivables (AppExp e1 e2) = do 
    map1 <- sends receivables e1 
    map2 <- sends receivables e2
    vs1  <- partition receivables e1
    vs2  <- partition receivables e2
    map3 <- applySends (Set.toList vs1) (Set.toList vs2)
    return $ Map.unionWith Set.union (Map.unionWith Set.union map1 map2) map3
    where
        -- We are only interested in functions with a body
        getExps (MatchVal body) v2      = matchBody body v2
        getExps (RecMatchVal x body) v2 = matchBody (substitute body (Map.singleton x (MatchVal body))) v2
        getExps _ _                     = Set.empty

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
            maps   <- Prelude.mapM (sends receivables) $ Set.toList es
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty maps

    
sends _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = return Map.empty

-- For invariants, we use the snapshots function to find the possible variants of the fail-body.
-- We may synchronize in either e1 or any variants of the fail body, so we apply sends recursively.
sends receivables (InvarExp _ _ subst e1 e2) = do 
    map1    <- sends receivables e1
    sigmas  <- snapshots receivables subst e1
    mapList <- Prelude.sequence [sends receivables (substitute e2 sigma) | sigma <- Set.toList sigmas]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

-- Let expressions are similar to invariants,
-- except we apply the partition function to find all possible values 'x' may be.
-- We then apply sends recursively on e1 and on all variants of e2.
sends receivables (LetExp x e1 e2) = do 
    map1    <- sends receivables e1
    vs1     <- partition receivables e1
    mapList <- Prelude.sequence [sends receivables (substitute e2 (Map.singleton x v)) | v <- Set.toList vs1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

-- In a synchronization expression, we may synchronize in all branching expressions,
-- so we call sends recursively on these.
-- Furthermore, we must account for all 'sending synchronizations'.
-- For each of these, we determine the possible values we may send,
-- and return a singleton map from the corresponding channel to the possible values.
sends receivables (SyncExp body) = sendsBody body
    where
        sendsBody :: SyncBody -> Maybe (Map Integer (Set Val))
        sendsBody (SingleSync q e)    = sendsSync q e 
        sendsBody (MultiSync q e rem) = do 
            map1 <- sendsSync q e
            map2 <- sendsBody rem
            return $ Map.unionWith Set.union map1 map2

        sendsSync :: Sync -> Exp -> Maybe (Map Integer (Set Val))
        sendsSync (SendSync (Right (SendVal id)) _ (Just v)) e = do
            map1 <- sends receivables e
            return $ Map.unionWith Set.union (Map.singleton id $ Set.singleton v) map1

        sendsSync (ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            mapList <- Prelude.sequence [sends receivables (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty mapList

        sendsSync (ReceiveSync (Right (ReceiveVal _)) _) _ = return Map.empty
        sendsSync (GetSync (Right (InPinVal _)) _) e       = sends receivables e
        sendsSync (SetSync (Right (OutPinVal _)) _) e      = sends receivables e

        sendsSync _ _ = mzero

sends receivables (GuardExp e _) = sends receivables e

-- We may synchronize in a nested parallel composition,
-- so we call sends recursively on e1 and e2.
sends receivables (ParExp e1 e2) = do 
    map1 <- sends receivables e1 
    map2 <- sends receivables e2
    return $ Map.unionWith Set.union map1 map2

-- None of the valid patterns were matched, fail.
sends _ _ = mzero
