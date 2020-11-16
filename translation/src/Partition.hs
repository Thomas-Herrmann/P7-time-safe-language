module Partition
    ( Partition.partition
    , match
    , sends
    , snapshots
    ) where

import Data.Set as Set
import Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.State as State
import Data.Foldable
import Ast


type ParT a = MaybeT (State Integer) a


partition :: Map Integer (Set Val) -> Exp -> Integer -> Maybe (Set Val, Integer)
partition receivables e n = 
    case runState (runMaybeT (partitionExp receivables e)) n of
        (Nothing, _)  -> Nothing
        (Just set, s) -> Just (set, s)


next :: ParT Integer
next = State.get >>= (\n -> State.put (n + 1) >> return n)


partitionExp :: Map Integer (Set Val) -> Exp -> ParT (Set Val)
partitionExp _ (ValExp v) = return $ Set.singleton v
partitionExp _ (RefExp _) = return Set.empty
partitionExp _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = return Set.empty
partitionExp receivables (GuardExp e _) = partitionExp receivables e
partitionExp receivables (LetExp x e1 e2) = partitionExp receivables e1 >>= foldrM fun Set.empty
    where
        fun v set = (partitionExp receivables . substitute e2) (Map.singleton x v) >>= return . (Set.union set)

partitionExp receivables (SyncExp body) = partitionBody body
    where
        partitionBody :: SyncBody -> ParT (Set Val)
        partitionBody (SingleSync q e)    = partitionSync q e
        partitionBody (MultiSync q e rem) = do
            set  <- partitionSync q e
            set' <- partitionBody rem
            return $ set `Set.union` set'

        partitionSync :: Sync -> Exp -> ParT (Set Val)
        partitionSync (ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            setList <- Prelude.sequence [partitionExp receivables (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            return $ Prelude.foldr Set.union Set.empty setList

        partitionSync (ReceiveSync (Right (ReceiveVal _)) _) _    = return Set.empty
        partitionSync (SendSync (Right (SendVal _)) _ (Just _)) e = partitionExp receivables e
        partitionSync (GetSync (Right (InPinVal _)) _) e          = partitionExp receivables e
        partitionSync (SetSync (Right (OutPinVal _)) _) e         = partitionExp receivables e

        partitionSync _ _ = mzero

partitionExp receivables (ParExp e1 e2) = do
    set1 <- partitionExp receivables e1
    set2 <- partitionExp receivables e2
    return $ Set.fromList [TermVal "Pair" [v1, v2] | v1 <- Set.toList set1, v2 <- Set.toList set2]

partitionExp receivables (InvarExp _ _ subst e1 e2) = do
    set1    <- partitionExp receivables e1
    sigmas  <- snapshotsExp receivables subst e1
    let e2' = substitute e2 subst
    setList <- Prelude.sequence [partitionExp receivables (substitute e2' sigma) | sigma <- Set.toList sigmas]
    return $ Prelude.foldr Set.union set1 setList

partitionExp receivables (AppExp e1 e2) = partitionExp receivables e1 >>= foldrM unionApply Set.empty
    where
        unionApply v set       = apply v e2 >>= return . (Set.union set) 
        unionMatch body v set  = matchBody body v >>= return . (Set.union set)

        apply :: Val -> Exp -> ParT (Set Val)
        apply (MatchVal body) e2   = partitionExp receivables e2 >>= foldrM (unionMatch body) Set.empty
        apply (TermVal x vs) e2    = partitionExp receivables e2 >>= (\set -> return (Set.fromList [TermVal x (vs ++ [v]) | v <- Set.toList set]))
        apply (ConVal ResetCon) e2 = partitionExp receivables e2
        apply (ConVal OpenCon) e2  = do 
            id  <- next
            set <- partitionExp receivables e2
            return $ Set.map (\v -> TermVal "Triple" [SendVal id, ReceiveVal id, v]) set

        matchBody :: MatchBody -> Val -> ParT (Set Val)
        matchBody (SingleMatch p e) v =
            case match p v of
                Nothing    -> return Set.empty
                Just sigma -> partitionExp receivables $ substitute e sigma
        matchBody (MultiMatch p e rem) v =
            case match p v of
                Nothing    -> matchBody rem v
                Just sigma -> do
                    set  <- partitionExp receivables $ substitute e sigma
                    set' <- matchBody rem v
                    return $ set `Set.union` set'

partitionExp _ _ = mzero


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


snapshots :: Map Integer (Set Val) -> Subst -> Exp -> Integer -> Maybe (Set Subst, Integer)
snapshots receivables subst e n = 
    case runState (runMaybeT (snapshotsExp receivables subst e)) n of
        (Nothing, _)  -> Nothing
        (Just map, s) -> Just (map, s)


snapshotsExp :: Map Integer (Set Val) -> Subst -> Exp -> ParT (Set Subst)
snapshotsExp receivables subst e = do
    possibilityMap <- snapshotsAux receivables e
    return $ cartesianProduct $ Map.mapWithKey addDefault possibilityMap
    where
        cartesianProduct :: Map Name (Set Val) -> Set Subst
        cartesianProduct possibilityMap = Map.foldrWithKey addBindings (Set.singleton Map.empty) possibilityMap

        addBindings x vs sigmas = Set.fromList [Map.insert x v sigma | v <- Set.toList vs, sigma <- Set.toList sigmas]

        addDefault x vs | x `Map.member` subst = vs `Set.union` Set.fromList [TermVal "Nothing" [], subst ! x]
                        | otherwise            = vs `Set.union` Set.singleton (TermVal "Nothing" [])


snapshotsAux :: Map Integer (Set Val) -> Exp -> ParT (Map Name (Set Val))
snapshotsAux _ (ValExp _)               = return Map.empty
snapshotsAux _ (RefExp _)               = return Map.empty
snapshotsAux receivables (AppExp e1 e2) = do
    map1 <- snapshotsAux receivables e1
    map2 <- snapshotsAux receivables e2
    vs1  <- partitionExp receivables e1
    vs2  <- partitionExp receivables e2
    map3 <- applySnapshots (Set.toList vs1) (Set.toList vs2)
    return $ Map.unionWith Set.union (Map.unionWith Set.union map1 map2) map3
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

        applySnapshots :: [Val] -> [Val] -> ParT (Map Name (Set Val))
        applySnapshots vs1 vs2 = do
            let es = Prelude.foldr Set.union Set.empty [getExps v1 v2 | v1 <- vs1, v2 <- vs2]
            maps   <- Prelude.mapM (snapshotsAux receivables) $ Set.toList es
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty maps


snapshotsAux _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = return Map.empty

snapshotsAux receivables (InvarExp _ _ subst e1 e2) = do
    map1    <- snapshotsAux receivables e1
    set1    <- snapshotsExp receivables subst e1
    mapList <- Prelude.sequence [snapshotsAux receivables (substitute e2 sigma) | sigma <- Set.toList set1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

snapshotsAux receivables (LetExp x e1 e2) = do
    map1    <- snapshotsAux receivables e1
    vs1     <- partitionExp receivables e1
    mapList <- Prelude.sequence [snapshotsAux receivables (substitute e2 (Map.singleton x v)) | v <- Set.toList vs1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

snapshotsAux receivables (SyncExp body) = snapshotsBody body
    where
        snapshotsBody (SingleSync q e)    = snapshotsSync q e
        snapshotsBody (MultiSync q e rem) = do 
            map1 <- snapshotsSync  q e
            map2 <- snapshotsBody rem
            return $ Map.unionWith Set.union map1 map2

        snapshotsSync (ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            let map1 = Map.singleton x $ receivables ! id
            mapList <- Prelude.sequence [snapshotsAux receivables (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

        snapshotsSync (ReceiveSync (Right (ReceiveVal _)) _) _ = return Map.empty
        snapshotsSync (ReceiveSync _ _) _                       = mzero

        snapshotsSync _ e = snapshotsAux receivables e

snapshotsAux receivables (GuardExp e _) = snapshotsAux receivables e

snapshotsAux receivables (ParExp e1 e2) = do
    map1 <- snapshotsAux receivables e1
    map2 <- snapshotsAux receivables e2
    return $ Map.unionWith Set.union map1 map2

snapshotsAux _ _ = mzero


sends :: Map Integer (Set Val) -> Exp -> Integer -> Maybe (Map Integer (Set Val), Integer) -- TODO: add receivables?
sends receivables e n = 
    case runState (runMaybeT (sendsExp receivables e)) n of
        (Nothing, _)  -> Nothing
        (Just map, s) -> Just (map, s)


sendsExp :: Map Integer (Set Val) -> Exp -> ParT (Map Integer (Set Val))
sendsExp _ (ValExp _)               = return Map.empty
sendsExp _ (RefExp _)               = return Map.empty
sendsExp receivables (AppExp e1 e2) = do 
    map1 <- sendsExp receivables e1 
    map2 <- sendsExp receivables e2
    vs1  <- partitionExp receivables e1
    vs2  <- partitionExp receivables e2
    map3 <- applySends (Set.toList vs1) (Set.toList vs2)
    return $ Map.unionWith Set.union (Map.unionWith Set.union map1 map2) map3
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
            maps   <- Prelude.mapM (sendsExp receivables) $ Set.toList es
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty maps

    
sendsExp _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = return Map.empty

sendsExp receivables (InvarExp _ _ subst e1 e2) = do 
    map1    <- sendsExp receivables e1
    sigmas  <- snapshotsExp receivables subst e1
    mapList <- Prelude.sequence [sendsExp receivables (substitute e2 sigma) | sigma <- Set.toList sigmas]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

sendsExp receivables (LetExp x e1 e2) = do 
    map1    <- sendsExp receivables e1
    vs1     <- partitionExp receivables e1
    mapList <- Prelude.sequence [sendsExp receivables (substitute e2 (Map.singleton x v)) | v <- Set.toList vs1]
    return $ Prelude.foldr (Map.unionWith Set.union) map1 mapList

sendsExp receivables (SyncExp body) = sendsBody body -- TODO: multiple passes!
    where
        sendsBody :: SyncBody -> ParT (Map Integer (Set Val))
        sendsBody (SingleSync q e)    = sendsSync q e 
        sendsBody (MultiSync q e rem) = do 
            map1 <- sendsSync q e
            map2 <- sendsBody rem
            return $ Map.unionWith Set.union map1 map2

        sendsSync :: Sync -> Exp -> ParT (Map Integer (Set Val))
        sendsSync (SendSync (Right (SendVal id)) _ (Just v)) e = do
            map1 <- sendsExp receivables e
            return $ Map.unionWith Set.union (Map.singleton id $ Set.singleton v) map1

        sendsSync (ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            mapList <- Prelude.sequence [sendsExp receivables (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            return $ Prelude.foldr (Map.unionWith Set.union) Map.empty mapList

        sendsSync (ReceiveSync (Right (ReceiveVal _)) _) _ = return Map.empty
        sendsSync (GetSync (Right (InPinVal _)) _) e       = sendsExp receivables e
        sendsSync (SetSync (Right (OutPinVal _)) _) e      = sendsExp receivables e

        sendsSync _ _ = mzero


sendsExp receivables (GuardExp e _) = sendsExp receivables e

sendsExp receivables (ParExp e1 e2) = do 
    map1 <- sendsExp receivables e1 
    map2 <- sendsExp receivables e2
    return $ Map.unionWith Set.union map1 map2

sendsExp _ _ = mzero
