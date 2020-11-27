module Partition
    ( Partition.partition
    , match
    , sends
    , multiPassSends
    , snapshots
    ) where

import Data.Set as Set
import Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.State as State
import Data.Functor((<&>))
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
partitionExp _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat x) (ValExp (MatchVal body)))))) = return $ Set.singleton (RecMatchVal x body)
partitionExp receivables (GuardExp e _) = partitionExp receivables e
partitionExp receivables (LetExp x e1 e2) = partitionExp receivables e1 >>= foldrM fun Set.empty
    where
        fun v set = (partitionExp receivables . substitute e2) (Map.singleton x v) <&> Set.union set

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
    let e2' = substitute e2 subst -- TODO: verify that this is right?
    setList <- Prelude.sequence [partitionExp receivables (substitute e2' sigma) | sigma <- Set.toList sigmas]
    return $ Prelude.foldr Set.union set1 setList

partitionExp receivables (AppExp e1 e2) = partitionExp receivables e1 >>= foldrM unionApply Set.empty
    where
        unionApply v set       = apply v <&> Set.union set
        unionMatch body        = partitionExp receivables e2 >>= matchBody body

        apply :: Val -> ParT (Set Val)
        apply (MatchVal body)      = unionMatch body
        apply (RecMatchVal x body) = unionMatch $ substitute body (Map.singleton x (MatchVal body)) -- Perform recursion once to hopefully find all value patterns
        apply (TermVal x vs)       = partitionExp receivables e2 >>= (\set -> return (Set.fromList [TermVal x (vs ++ [v]) | v <- Set.toList set]))
        apply (ConVal ResetCon)    = partitionExp receivables e2
        apply (ConVal OpenCon)     = do 
            id  <- next
            set <- partitionExp receivables e2
            return $ Set.map (\v -> TermVal "Triple" [SendVal id, ReceiveVal id, v]) set

        matchSet :: Pat -> Exp -> Set Val -> ParT (Set Val)
        matchSet p e set = foldrM (\v set' -> matchf v <&> Set.union set') Set.empty $ Set.toList set
            where
                    matchf v =    
                        case match p v of
                            Nothing    -> return Set.empty
                            Just sigma -> partitionExp receivables $ substitute e sigma

        matchBody :: MatchBody -> Set Val -> ParT (Set Val)
        matchBody (SingleMatch p e) set = do 
            set' <- matchSet p e set
            when (Set.null set') mzero -- TODO: verify that this fails!
            return set'

        matchBody (MultiMatch p e rem) set = do 
            set' <- matchSet p e set 
            when (Set.null set') mzero -- TODO: verify that this fails!
            matchBody rem set <&> Set.union set'

partitionExp _ _ = mzero


match :: Pat -> Val -> Maybe Subst
match (RefPat x) v                                                           = Just $ Map.singleton x v
match (TermPat _ ps) (TermVal _ vs) | Prelude.length ps == Prelude.length vs = Prelude.foldr accumulator (Just Map.empty) $ Prelude.zip ps vs
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
        snapshotsSync (ReceiveSync _ _) _                      = mzero

        snapshotsSync _ e = snapshotsAux receivables e

snapshotsAux receivables (GuardExp e _) = snapshotsAux receivables e

snapshotsAux receivables (ParExp e1 e2) = do
    map1 <- snapshotsAux receivables e1
    map2 <- snapshotsAux receivables e2
    return $ Map.unionWith Set.union map1 map2

snapshotsAux _ _ = mzero


multiPassSends :: Exp -> Exp -> Integer -> Integer -> Maybe (Map Integer (Set Val), Map Integer (Set Val), Integer)
multiPassSends e1 e2 passes n =
    case runState (runMaybeT (multiPassAux e1 e2 Map.empty Map.empty passes)) n of
        (Nothing, _)           -> Nothing
        (Just (map1, map2), s) -> Just (map1, map2, s)
    where
        multiPassAux :: Exp -> Exp -> Map Integer (Set Val) -> Map Integer (Set Val) -> Integer -> ParT (Map Integer (Set Val), Map Integer (Set Val))
        multiPassAux _ _ receivables1 receivables2 n | n <= 1    = return (receivables2, receivables1)
                                                     | otherwise = do
            map1 <- sendsExp receivables1 e1
            map2 <- sendsExp receivables2 e2
            multiPassAux e1 e2 map2 map1 $ n - 1


sends :: Map Integer (Set Val) -> Exp -> Integer -> Maybe (Map Integer (Set Val), Integer)
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

sendsExp receivables (SyncExp body) = sendsBody body
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
