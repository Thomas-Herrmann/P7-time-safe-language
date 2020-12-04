{-# LANGUAGE OverloadedStrings #-}
module Translate
    ( translate
    ) where

import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Control.Monad.Trans.Maybe
import Control.Monad.State as State
import Data.Text as Text
import Data.Functor((<&>))
import Control.Monad.IO.Class(liftIO)
import Ast
import Partition
import Uppaal

data TransState = TransState {
                               shouldPrune :: Bool
                             , minMaxD     :: Maybe (Integer, Integer)
                             , clockDStack :: [Text]
                             , uniqueID    :: Integer
                             , tempID      :: Integer
                             , locID       :: Integer
                             , clockID     :: Integer
                             , staticMap   :: Map Val Text
                             }

type TransT a = MaybeT (StateT TransState IO) a


liftMaybe :: Maybe a -> MaybeT (StateT TransState IO) a
liftMaybe = maybe mzero return


translate :: Bool -> Maybe (Integer, Integer) -> Exp -> [Name] -> [Name] -> [Name] -> [(Name, Name)] -> IO (Maybe System)
translate pruneFlag minMaxD e clockNames inPinNames outPinNames chanNames = do
    maybe <- runStateT (runMaybeT (translateExp Map.empty Map.empty Map.empty [] e' >>= prune)) initState
    case maybe of
        (Nothing, _)                   -> return Nothing
        (Just (temp, sys, map), state) -> do
            let finTrans = Transition "Terminated" "Terminated" [] : Map.foldr (\set l -> [Transition id "Terminated" [] | id <- Set.toList set] ++ l) [] map
            let temp'    = temp{  temLocations   = Location "Terminated"  [] (Just "Terminated") NormalType : temLocations temp,
                                  temTransitions = temTransitions temp ++ finTrans }
            return $ Just sys{ sysTemplates   = temp' : sysTemplates sys, 
                               sysDecls       = "clock clkD1;\n" : sysDecls sys ++ stateDecls (staticMap state),
                               sysSystemDecls = makeSysDecls (temp : sysTemplates sys) }
    where
        clocks n       = ClkVal n : clocks (n + 1)
        inPins n       = InPinVal n : inPins (n + 1)
        outPins n      = OutPinVal n : outPins (n + 1)
        channels n     = (SendVal n, ReceiveVal n) : channels (n + 1)
        clockSubst     = Map.fromList $ Prelude.zip clockNames $ clocks 0
        inPinsSubst    = Map.fromList $ Prelude.zip inPinNames $ inPins 0
        outPinsSubst   = Map.fromList $ Prelude.zip outPinNames $ outPins 0
        (chanSubst, _) = Prelude.foldr (\(sn, rn) (map, (s, r):chs) -> (map `Map.union` Map.fromList [(sn, s), (rn, r)], chs)) (Map.empty, channels 0) chanNames
        clockMap       = Map.fromList $ Prelude.zip (clocks 0) $ Prelude.map Text.pack clockNames
        inPinMap       = Map.fromList $ Prelude.zip (inPins 0) $ Prelude.map Text.pack inPinNames
        outPinMap      = Map.fromList $ Prelude.zip (outPins 0) $ Prelude.map Text.pack outPinNames
        initState      = TransState pruneFlag minMaxD ["clkD1"] 0 0 0 2 $ clockMap `Map.union` inPinMap `Map.union` outPinMap
        e'             = substitute e $ clockSubst `Map.union` inPinsSubst `Map.union` outPinsSubst `Map.union` chanSubst

        stateDecls :: Map Val Text -> [Declaration]
        stateDecls map = Map.foldrWithKey makeDecl [] map

        makeDecl (ClkVal _) t decls    = (Text.pack "clock " `Text.append` t `Text.append` Text.pack ";\n") : decls
        makeDecl (SendVal _) t decls   = (Text.pack "chan " `Text.append` t `Text.append` Text.pack ";\n") : decls
        makeDecl (InPinVal _) t decls  = (Text.pack "bool " `Text.append` t `Text.append` Text.pack " = 0;\n") : decls
        makeDecl (OutPinVal _) t decls = (Text.pack "bool " `Text.append` t `Text.append` Text.pack " = 0;\n") : decls
        makeDecl _ _ decls             = decls

        makeSysDecls :: [Template] -> [Declaration]
        makeSysDecls temps =
            let tempNames        = Prelude.map temName temps
                foldf name decls = ("P_" `Text.append` name `Text.append` " = " `Text.append` name `Text.append` "();\n"):decls
                tempDecls        = Prelude.foldr foldf [] tempNames
                sysDecl          = "system " `Text.append` Text.pack (List.intercalate ", " (Prelude.map ((++) "P_" . Text.unpack) tempNames)) `Text.append` ";"
            in tempDecls ++ [sysDecl]


joinSys :: System -> System -> System
sys1 `joinSys` sys2 = sys1{ 
    sysDecls       = sysDecls sys1 ++ sysDecls sys2,
    sysTemplates   = sysTemplates sys1 ++ sysTemplates sys2,
    sysSystemDecls = sysSystemDecls sys1 ++ sysSystemDecls sys2,
    sysQueries     = sysQueries sys1 ++ sysQueries sys2
 }


joinTemp :: Template -> Template -> Template
temp1 `joinTemp` temp2 = temp1{
    temLocations   = temLocations temp1 ++ temLocations temp2,
    temTransitions = temTransitions temp1 ++ temTransitions temp2,
    temDecls       = temDecls temp1 ++ temDecls temp2
}


putClkD :: TransT Text
putClkD = do
    state    <- State.get
    let name = "clkD" `Text.append` Text.pack (show (clockID state))
    put state{ clockDStack = name : clockDStack state, clockID = 1 + clockID state }
    return $ "clock " `Text.append` name `Text.append` ";\n"

popClkD :: TransT ()
popClkD = do
    state <- State.get
    let _:clks = clockDStack state
    put state{ clockDStack = clks }


addMinMaxEdge :: [Transition] -> TransT [Transition]
addMinMaxEdge edges = do
    minMaxD <- State.get <&> minMaxD
    clk:_   <- State.get <&> clockDStack
    return $ case minMaxD of
        Nothing        -> edges
        Just (minD, _) -> Prelude.map (addUpdate clk . addGuard (Label GuardKind $ clk `Text.append` " >= " `Text.append` Text.pack (show minD))) edges
    where
        addUpdate clk (Transition to from labels) =
            let (label', labels') = Prelude.foldr updateLabels (Label AssignmentKind (clk `Text.append` " := 0"), []) labels 
            in Transition to from $ label' : labels' 
        
        updateLabels (Label AssignmentKind text) (Label AssignmentKind text', labels) = (Label AssignmentKind $ text `Text.append` ", " `Text.append` text', labels)
        updateLabels label' (label, labels)                                           = (label, label' : labels)


addClockDResetEdge :: [Transition] -> TransT [Transition]
addClockDResetEdge edges = do
    state <- State.get
    let clk:_ = clockDStack state
    minMaxD <- State.get <&> minMaxD
    return $ case minMaxD of
        Nothing -> edges
        Just _  -> Prelude.map (addUpdate clk) edges
    where
        addUpdate clk (Transition to from labels) =
            let (label', labels') = Prelude.foldr updateLabels (Label AssignmentKind (clk `Text.append` " := 0"), []) labels 
            in Transition to from $ label' : labels' 
        
        updateLabels (Label AssignmentKind text) (Label AssignmentKind text', labels) = (Label AssignmentKind $ text `Text.append` ", " `Text.append` text', labels)
        updateLabels label' (label, labels)                                           = (label, label' : labels)


addMinMaxLoc :: [Location] -> TransT [Location]
addMinMaxLoc locs = do
    state <- State.get
    let clk:_ = clockDStack state
    minMaxD <- State.get <&> minMaxD
    return $ case minMaxD of
        Nothing        -> locs
        Just (_, maxD) -> Prelude.map (addInvariant $ Label InvariantKind $ clk `Text.append` " < " `Text.append` Text.pack (show maxD)) locs



prune :: (Template, System, Map Val (Set Text)) -> TransT (Template, System, Map Val (Set Text))
prune (temp, sys, map) = do
    state <- State.get
    let clk:_ = clockDStack state
    if shouldPrune state
        then return (pruneTemplate clk temp, sys, map)
        else return (temp, sys, map) -- Do no pruning


nilSystem :: Text -> TransT (Template, System)
nilSystem t = do
    name <- nextTempName
    loc  <- newLoc t
    locs <- addMinMaxLoc [loc]
    return (Template name locs [] [] (locId loc) (locId loc), System [] [] [] [])


cttToInvariant :: Ctt -> Ctt
cttToInvariant (LandCtt g1 g2)   = LandCtt (cttToInvariant g1) (cttToInvariant g2)
cttToInvariant (ClockLeqCtt x n) = ClockLeqCtt x $ n + 1
cttToInvariant (ClockGeqCtt x n) = ClockGeqCtt x $ n - 1
cttToInvariant (ClockLCtt x n)   = ClockLeqCtt x n
cttToInvariant (ClockGCtt x n)   = ClockGeqCtt x n
cttToInvariant (LorCtt _ _)      = error "Logical OR may only be used on fail edges!"


translateCtt :: Ctt -> TransT [Label]
translateCtt (LandCtt g1 g2) = do
    lbs1 <- translateCtt g1
    lbs2 <- translateCtt g2
    return [Label GuardKind (t1 `Text.append` " and " `Text.append` t2) | Label _ t1 <- lbs1, Label _ t2 <- lbs2]

translateCtt (LorCtt g1 g2) = do
    lbs1 <- translateCtt g1
    lbs2 <- translateCtt g2
    return $ Prelude.concat [[Label GuardKind t1, Label GuardKind t2] | Label _ t1 <- lbs1, Label _ t2 <- lbs2]

translateCtt (ClockLeqCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return [Label GuardKind (t `Text.append` Text.pack (" <= " ++ show n))])

translateCtt (ClockGeqCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return [Label GuardKind (t `Text.append` Text.pack (" >= " ++ show n))])

translateCtt (ClockLCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return [Label GuardKind (t `Text.append` Text.pack (" < " ++ show n))])

translateCtt (ClockGCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return [Label GuardKind (t `Text.append` Text.pack (" > " ++ show n))])

translateCtt _ = liftIO $ print "1" >> mzero


translateExp :: Subst -> Map Name (Text, Text) -> Map Integer (Set Val) -> [([Label], Label)] -> Exp -> TransT (Template, System, Map Val (Set Text))
translateExp _ _ _ _ (ValExp v) = do 
    state       <- State.get
    (temp, sys) <- nilSystem $ locNameFromVal (staticMap state) v
    return (temp, sys, Map.singleton v $ Set.singleton (temInit temp))

-- fix has no effect unless applied, as we force it to be wrapped around abstractions!
translateExp _ _ _ _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat x) (ValExp (MatchVal body)))))) = do 
    (temp, sys) <- nilSystem "fixAbs"
    return (temp, sys, Map.singleton (RecMatchVal x body) $ Set.singleton (temInit temp))

translateExp recSubst recVars receivables inVars (AppExp (RefExp x) e2) | x `Map.notMember` recSubst = liftIO $ print "2" >>  mzero
                                                                        | otherwise                  = do
    (temp1, sys1)            <- nilSystem $ "recRef_" `Text.append` Text.pack x `Text.append` "_"
    (temp2, sys2, map1)      <- translateExp recSubst recVars receivables inVars e2
    locFinal                 <- newLoc $ "recRefFinish_" `Text.append` Text.pack x `Text.append` "_" 
    mappedLocs               <- addMinMaxLoc [locFinal]
    let (recInit, recFinish) = recVars ! x
    recTrans                 <- addMinMaxEdge [Transition (temInit temp1) recInit [], Transition recFinish (locId locFinal) []]
    let temp1'               = temp1{ temLocations   = mappedLocs ++ temLocations temp1,
                                      temTransitions = temTransitions temp1 ++ recTrans }
    let tempRes              = temp2 `joinTemp` temp1'
    newTrans                 <- addMinMaxEdge $ Map.foldr (\set l -> [Transition id (temInit temp1') [] | id <- Set.toList set] ++ l) [] map1
    let tempRes'             = tempRes{ temTransitions = newTrans ++ temTransitions tempRes }
    prune (tempRes', sys2 `joinSys` sys1, Map.map (\_ -> Set.singleton (locId locFinal)) map1)

translateExp recSubst recVars receivables inVars (AppExp e1 e2) = do
    (temp1, sys1, map1) <- translateExp recSubst recVars receivables inVars e1
    (temp2, sys2, map2) <- translateExp recSubst recVars receivables inVars e2
    let vs1             = Map.keys map1
    let vs2             = Map.keys map2
    branchLoc           <- newLoc "branch"
    bJoinLoc            <- newLoc "branchJoin"
    mappedLocs          <- addMinMaxLoc [branchLoc, bJoinLoc]
    case () of
        _ | Map.size map1 > 1 || Map.size map2 > 1 -> do
            (intValMap1, var1)  <- setUpVarBranch map1
            (intValMap2, var2)  <- setUpVarBranch map2
            let varDecl         = "int " `Text.append` var1 `Text.append` ", " `Text.append` var2 `Text.append` ";\n"
            systemSets          <- Prelude.sequence [addGuardToSet (locId branchLoc) var1 var2 (intValMap1 ! v1) (intValMap2 ! v2) $ apply v1 v2 (locId branchLoc) (locId bJoinLoc) | v1 <- vs1, v2 <- vs2]
            let systems         = Prelude.foldr Set.union Set.empty systemSets
            let temp3           = temp1 `joinTemp` temp2
            newTrans            <- addMinMaxEdge $ makeAssignTrans map1 intValMap1 var1 (temInit temp2) ++ makeAssignTrans map2 intValMap2 var2 (locId branchLoc)
            let temp3'          = temp3{ temLocations   = temLocations temp3 ++ mappedLocs, 
                                         temTransitions = temTransitions temp3 ++ newTrans,
                                         temDecls       = varDecl : temDecls temp3 }
            prune $ Prelude.foldr joinTuples (temp3', sys1 `joinSys` sys2, Map.empty) systems
          | otherwise -> do
            systemSets          <- Prelude.sequence [addBranchToSet (locId branchLoc) $ apply v1 v2 (locId branchLoc) (locId bJoinLoc) | v1 <- vs1, v2 <- vs2]
            let systems         = Prelude.foldr Set.union Set.empty systemSets
            let temp3           = temp1 `joinTemp` temp2
            newTrans            <- addMinMaxEdge $ makePlainTrans (Map.elems map1) (temInit temp2) ++ makePlainTrans (Map.elems map2) (locId branchLoc)
            let temp3'          = temp3{ temLocations   = temLocations temp3 ++ mappedLocs, 
                                         temTransitions = temTransitions temp3 ++ newTrans }
            prune $ Prelude.foldr joinTuples (temp3', sys1 `joinSys` sys2, Map.empty) systems
    
    where
        joinTuples (t1, s1, m1) (t2, s2, m2) = (t2 `joinTemp` t1, s2 `joinSys` s1, Map.unionWith Set.union m2 m1)

        makePlainTrans sets to = Prelude.foldr (\set l -> [Transition id to [] | id <- Set.toList set] ++ l) [] sets

        makeAssignTrans map intMap var to = Map.foldrWithKey (\v set l -> [Transition id to [Label AssignmentKind (var `Text.append` " := " `Text.append` Text.pack (show (intMap ! v)))] | id <- Set.toList set] ++ l) [] map

        makeGuard var1 var2 id1 id2 = Label GuardKind $ var1 `Text.append` " == " `Text.append` Text.pack (show id1) `Text.append` " and " `Text.append`
                                                        var2 `Text.append` " == " `Text.append` Text.pack (show id2)

        addBranchToSet :: Text -> TransT (Set (Template, System, Map Val (Set Text))) -> TransT (Set (Template, System, Map Val (Set Text)))
        addBranchToSet from monad = do
            set    <- monad
            list   <- mapM (\(temp, sys, map) -> do 
                        branches <- addMinMaxEdge [Transition from (temInit temp) []]
                        return (temp{ temTransitions = branches ++ temTransitions temp }, sys, map)) $ Set.toList set
            return $ Set.fromList list

        addGuardToSet from var1 var2 id1 id2 monad = do
            set       <- monad
            let guard = makeGuard var1 var2 id1 id2
            list      <- mapM (\(temp, sys, map) -> do 
                            branches <- addMinMaxEdge [Transition from (temInit temp) [guard]]
                            return (temp{ temTransitions = branches ++ temTransitions temp }, sys, map)) $ Set.toList set
            return $ Set.fromList list

        setUpVarBranch :: Map Val (Set Text) -> TransT (Map Val Integer, Text)
        setUpVarBranch map = do
            let (intValMap, _) = Map.foldrWithKey (\v _ (map, n) -> (Map.insert v n map, n + 1)) (Map.empty, 0) map
            varId              <- nextUniqueID
            let varName        = "selector" `Text.append` Text.pack (show varId)
            return (intValMap, varName)

        matchBody :: MatchBody -> Val -> TransT (Set Exp)
        matchBody (SingleMatch p e) v =
            case match p v of
                Nothing    -> return Set.empty
                Just sigma -> return $ Set.singleton (substitute e sigma)
        matchBody (MultiMatch p e rem) v =
            case match p v of
                Nothing    -> matchBody rem v
                Just sigma -> do
                    let set = Set.singleton $ substitute e sigma
                    set'    <- matchBody rem v
                    return $ set `Set.union` set'

        apply :: Val -> Val -> Text -> Text -> TransT (Set (Template, System, Map Val (Set Text)))
        apply (MatchVal body) v2 _ _ = do
            es      <- matchBody body v2
            systems <- Prelude.mapM (translateExp recSubst recVars receivables inVars) (Set.toList es)
            return $ Set.fromList systems

        apply fun@(RecMatchVal x body) v2 recInit recFinal = do
            es               <- matchBody body v2
            let recVars'     = Map.insert x (recInit, recFinal) recVars
            let recSubst'    = Map.insert x fun recSubst
            let newTrans map = Map.foldr (\set monad -> do
                    l        <- monad 
                    branches <- addMinMaxEdge [Transition id recFinal [] | id <- Set.toList set]
                    return $ branches ++ l) (return []) map
            systems          <- Prelude.mapM (translateExp recSubst' recVars' receivables inVars) (Set.toList es)
            Prelude.mapM (\(temp, sys, map) -> do 
                    branches <- newTrans map
                    return (temp{ temTransitions = branches ++ temTransitions temp }, sys, map)) systems <&> Set.fromList

        apply v1@(TermVal name vs) v2 _ _ = do 
            state  <- State.get
            (temp, sys) <- nilSystem $ "app" `Text.append` locNameFromVal (staticMap state) v1
            return $ Set.singleton (temp, sys, Map.singleton (TermVal name $ vs ++ [v2]) (Set.singleton (temInit temp)))

        apply (ConVal ResetCon) v2 _ _ = do
            (temp, sys) <- nilSystem "appReset"
            finalLoc    <- newLoc "appDone"
            mappedLocs  <- addMinMaxLoc [finalLoc]
            t           <- translateStatic v2
            let label   = Label AssignmentKind $ t `Text.append` " = 0"
            newTrans    <- addMinMaxEdge [Transition (temInit temp) (locId finalLoc) [label]]
            return $ Set.singleton (temp{ temLocations   = mappedLocs ++ temLocations temp,
                                          temTransitions = newTrans ++ temTransitions temp }, 
                                    sys, Map.singleton v2 (Set.singleton (locId finalLoc)))

translateExp recSubst recVars receivables inVars (InvarExp g _ subst e1 e2) = do
    failLabels    <- translateCtt $ negateCtt g
    [guardLabel]  <- translateCtt g
    [Label _ t]   <- translateCtt $ cttToInvariant g
    locInit       <- newLoc "invarInit"
    locFail       <- newLoc "invarFail"
    mappedLocs    <- addMinMaxLoc [locInit, locFail]
    (temp1, sys1, map1) <- translateExp recSubst recVars receivables ((failLabels, Label InvariantKind t) : inVars) e1 >>= prune
    let temp1'    = temp1{ temLocations   = Prelude.map (addInvariant (Label InvariantKind t)) $ temLocations temp1,
                           temTransitions = Prelude.map (addGuard guardLabel) $ temTransitions temp1 }
    failTrans     <- addClockDResetEdge [Transition (locId loc) (locId locFail) [failLabel] | loc <- locInit : temLocations temp1, failLabel <- failLabels]
    (map1', succTrans, locs) <- foldM (makePair guardLabel map1) (Map.empty, [], []) $ Map.keys map1
    connTrans     <- addMinMaxEdge [Transition (locId locInit) (temInit temp1') []]
    let temp2     = temp1'{ temTransitions = temTransitions temp1' ++ failTrans ++ succTrans ++ connTrans,
                            temLocations   = temLocations temp1' ++ mappedLocs ++ locs,
                            temInit        = locId locInit }
    sigmas        <- liftMaybe $ snapshots receivables subst e1
    let e2'       = substitute e2 subst
    systems       <- Prelude.sequence [translateExp recSubst recVars receivables inVars (substitute e2' sigma) | sigma <- Set.toList sigmas]
    systems'      <- Prelude.mapM (\(temp, sys, map) -> do 
            link <- addMinMaxEdge [Transition (locId locFail) (temInit temp) []]
            return (temp{ temTransitions = link ++ temTransitions temp }, sys, map)) systems
    prune $ Prelude.foldr joinTuples (temp2, sys1, map1') systems' 
    where
        joinTuples (t1, s1, m1) (t2, s2, m2) = (t2 `joinTemp` t1, s2 `joinSys` s1, Map.unionWith Set.union m2 m1)

        makePair guard prevMap (map, ts, ls) v = do
            state     <- State.get
            loc       <- newLoc $ "invarSucc_" `Text.append` locNameFromVal (staticMap state) v
            mappedLoc <- addMinMaxLoc [loc]
            ts'       <- addMinMaxEdge [Transition id (locId loc) [guard] | id <- Set.toList $ prevMap ! v]
            return (Map.unionWith Set.union (Map.singleton v (Set.singleton (locId loc))) map, ts' ++ ts, mappedLoc ++ ls)

translateExp recSubst recVars receivables inVars (LetExp x e1 e2) = do
    (temp1, sys1, map1) <- translateExp recSubst recVars receivables inVars e1
    let vs1             = Map.keys map1
    systems             <- Prelude.sequence [addTransitions map1 v $ translateExp recSubst recVars receivables inVars (substitute e2 (Map.singleton x v)) | v <- vs1]
    prune $ Prelude.foldr joinTuples (temp1, sys1, Map.empty) systems
    where
        joinTuples (t1, s1, m1) (t2, s2, m2) = (t2 `joinTemp` t1, s2 `joinSys` s1, m2 `Map.union` m1)

        addTransitions :: Map Val (Set Text) -> Val -> TransT (Template, System, Map Val (Set Text)) -> TransT (Template, System, Map Val (Set Text))
        addTransitions map v monad | v `Map.notMember` map = liftIO $ print "3" >>  mzero
                                   | otherwise             = do
            (temp, sys, map') <- monad
            newTrans          <- addMinMaxEdge [Transition id (temInit temp) [] | id <- Set.toList $ map ! v]
            return (temp{ temTransitions = newTrans ++ temTransitions temp }, sys, map')

translateExp recSubst recVars receivables inVars (SyncExp body) = do
    (temp, sys) <- nilSystem "syncInit"
    systems     <- translateBody (temInit temp) body
    prune $ Prelude.foldr joinTuples (temp, sys, Map.empty) systems
    where
        joinTuples (t1, s1, m1) (t2, s2, m2) = (t2 `joinTemp` t1, s2 `joinSys` s1, m2 `Map.union` m1)

        translateBody from (SingleSync q e)    = translateSyncPair from q e
        translateBody from (MultiSync q e rem) = do 
            systems  <- translateSyncPair from q e
            systems' <- translateBody from rem
            return $ systems ++ systems'

        translateSyncPair from q@(ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            systems                       <- Prelude.sequence [translateExp recSubst recVars receivables inVars (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            label                         <- translateSync q
            let addGuard (temp, sys, map) = do 
                    link <- addClockDResetEdge [Transition from (temInit temp) [label]]
                    return (temp{ temTransitions = link ++ temTransitions temp }, sys, map)
            Prelude.mapM addGuard systems

        translateSyncPair _ (ReceiveSync (Right (ReceiveVal _)) _) _ = return []

        translateSyncPair from q e = do
            (temp, sys, map) <- translateExp recSubst recVars receivables inVars e
            label            <- translateSync q
            link             <- addClockDResetEdge [Transition from (temInit temp) [label]]
            return [(temp{ temTransitions = link ++ temTransitions temp }, sys, map)]

translateExp recSubst recVars receivables inVars (GuardExp e g) = do
    guard            <- translateCtt g
    [Label _ invar]  <- translateCtt $ cttToInvariant g
    (temp, sys, map) <- translateExp recSubst recVars receivables inVars e
    initLoc          <- newLoc "guardInit"
    mappedLoc        <- addMinMaxLoc [initLoc]
    clockResetTrans  <- do
            minMaxD <- State.get <&> minMaxD
            case minMaxD of
                Nothing -> return []
                _       -> addMinMaxEdge [Transition (locId initLoc) (locId initLoc) []]
    interLoc         <- newLoc "guardSatisfied" <&> \loc -> loc{ locLabels = [Label InvariantKind invar], locType = UrgentType }
    let initTrans    = Transition (locId initLoc) (locId interLoc) guard
    guardBreakTrans  <- addClockDResetEdge [Transition (locId interLoc) (temInit temp) guard]
    prune (temp{ temLocations   = interLoc : (mappedLoc ++ temLocations temp), 
                 temTransitions = clockResetTrans ++ [initTrans] ++ guardBreakTrans ++ temTransitions temp, 
                 temInit        = locId initLoc }, sys, map) -- we assume that our guards do not have LOR, although syntactically possible

translateExp _ _ receivables inVars (ParExp e1 e2) = do
    (sendables1, sendables2) <- liftMaybe $ multiPassSends e1 e2 2
    startID                  <- nextUniqueID
    stopID1                  <- nextUniqueID
    stopID2                  <- nextUniqueID
    clockDecl1               <- putClkD 
    (temp1, sys1, map1)      <- translateExp Map.empty Map.empty ((receivables `Map.union` sendables2) `Map.difference` sendables1) [] e1 >>= prune
    (intValMap1, var1)       <- setUpVarBranch map1
    temp1'                   <- addGuards temp1 intValMap1 map1 var1 startID stopID1 inVars
    popClkD
    clockDecl2               <- putClkD
    (temp2, sys2, map2)      <- translateExp Map.empty Map.empty ((receivables `Map.union` sendables1) `Map.difference` sendables2) [] e2 >>= prune
    (intValMap2, var2)       <- setUpVarBranch map2
    temp2'                   <- addGuards temp2 intValMap2 map2 var2 startID stopID2 inVars
    popClkD
    (tempMain, sys3)         <- nilSystem "parInit"
    let sys4                 = sys1 `joinSys` sys2 `joinSys` sys3
    (tempMain', mapRes)      <- addGuardsMain tempMain intValMap1 var1 intValMap2 var2 startID stopID1 stopID2
    let varDecl              = Text.pack $ "broadcast chan " ++ "start" ++ show startID ++ ";\n chan stop" ++ show stopID1 ++ ", stop" ++ show stopID2 ++ ";\n"
    let varDecl'             = "int " `Text.append` var1 `Text.append` ", " `Text.append` var2 `Text.append` ";\n" `Text.append` varDecl
    prune (tempMain', sys4{ sysTemplates = sysTemplates sys4 ++ [temp1', temp2'], 
                            sysDecls = clockDecl1 : clockDecl2 : varDecl' : sysDecls sys4 }, mapRes)
    where
        varText s id kind = Text.pack $ s ++ show id ++ kind

        setUpVarBranch :: Map Val (Set Text) -> TransT (Map Val Integer, Text)
        setUpVarBranch map = do
            let (intValMap, _) = Map.foldrWithKey (\v _ (map, n) -> (Map.insert v n map, n + 1)) (Map.empty, 0) map
            varId              <- nextUniqueID
            let varName        = "selector" `Text.append` Text.pack (show varId)
            return (intValMap, varName)

        addGuards temp intMap locMap var startID stopID inVars = do
            initLoc        <- newLoc "init"
            mappedLoc      <- addMinMaxLoc [initLoc]
            let vs         = Map.keys locMap
            let startLabel = Label SyncKind $ varText "start" startID "?"
            let endLabel   = Label SyncKind $ varText "stop" stopID "!"
            let foldf v l  = [Transition id (locId initLoc) [endLabel, Label AssignmentKind $ var `Text.append` " := " `Text.append` Text.pack (show (intMap ! v))] | id <- Set.toList $ locMap ! v] ++ l
            newTrans       <- addMinMaxEdge $ Transition (locId initLoc) (temInit temp) [startLabel] : Prelude.foldr foldf [] vs
            temp'          <- checkInvariant temp (locId initLoc) inVars
            let temp''     = Prelude.foldr (\(_, inVar) temp -> temp{ temLocations = Prelude.map (addInvariant inVar) $ temLocations temp }) temp' inVars
            return $ temp''{ temInit        = locId initLoc,
                             temLocations   = mappedLoc ++ temLocations temp'', 
                             temTransitions = temTransitions temp'' ++ newTrans }

        checkInvariant temp to inVars = do
            failTrans <- addClockDResetEdge $ Prelude.concat [[Transition from to [failLabel] | failLabel <- failLabels, from <- Prelude.map locId $ temLocations temp] | (failLabels, _) <- inVars]
            return temp{ temTransitions = temTransitions temp ++ failTrans }

        addGuardsMain temp intValMap1 var1 intValMap2 var2 startID stopID1 stopID2 = do
            initLoc                <- newLoc "parInit"
            stopLoc1               <- newLoc "parStopA"
            stopLoc2               <- newLoc "parStopB"
            let startLabel         = Label SyncKind $ varText "start" startID "!"
            let endLabel1          = Label SyncKind $ varText "stop" stopID1 "?"
            let endLabel2          = Label SyncKind $ varText "stop" stopID2 "?"
            let vs1                = Map.keys intValMap1
            let vs2                = Map.keys intValMap2
            branchPairs            <- Prelude.sequence [makePair (locId stopLoc2) v1 v2 | v1 <- vs1, v2 <- vs2]
            let newLocs            = Prelude.map (snd . fst) branchPairs
            mappedLocs             <- addMinMaxLoc $ initLoc : stopLoc2 : newLocs
            let (locMap, newTrans) = Prelude.foldr (\((v, loc), t) (map, ts) -> (Map.insert v (Set.singleton (locId loc)) map, t:ts)) (Map.empty, []) branchPairs
            finTrans               <- addClockDResetEdge $ Transition (locId initLoc) (temInit temp) [startLabel] : [Transition (locId stopLoc1) (locId stopLoc2) [endLabel2]]
            mappedTrans            <- addMinMaxEdge newTrans
            let newTrans'          = Transition (temInit temp) (locId stopLoc1) [endLabel1] : mappedTrans ++ finTrans
            return (temp{ temInit        = locId initLoc,
                          temLocations   = stopLoc1 : temLocations temp ++ mappedLocs,
                          temTransitions = temTransitions temp ++ newTrans' }, locMap)
            where
                makePair from v1 v2 = do
                    state <- State.get
                    loc <- newLoc $ "parFin_" `Text.append` locNameFromVal (staticMap state) v1 `Text.append` "_" `Text.append` locNameFromVal (staticMap state) v2
                    let label = Label GuardKind $ var1 `Text.append` " == " `Text.append` Text.pack (show (intValMap1 ! v1)) `Text.append` " and " `Text.append`
                                                  var2 `Text.append` " == " `Text.append` Text.pack (show (intValMap2 ! v2))
                    let trans = Transition from (locId loc) [label]
                    return ((TermVal "Pair" [v1, v2], loc), trans)
                                                  

translateExp _ _ _ _ e = liftIO $ print e >>  mzero


addInvariant :: Label -> Location -> Location
addInvariant invar loc =
    let (label, labels) = Prelude.foldr extendInvar (invar, []) $ locLabels loc
    in  loc{ locLabels = label : labels }
    where
        extendInvar (Label InvariantKind t') (Label _ t, labels) = (Label InvariantKind $ t' `Text.append` " and " `Text.append` t, labels)
        extendInvar label' (label, labels)                       = (label, label' : labels) 


addGuard :: Label -> Transition -> Transition
addGuard guard (Transition from to existing) =
    let (label, labels) = Prelude.foldr extendGuard (guard, []) existing
    in  Transition from to $ label : labels
    where
        extendGuard (Label GuardKind t') (Label _ t, labels) = (Label GuardKind $ t' `Text.append` " and " `Text.append` t, labels)
        extendGuard label' (label, labels)                   = (label, label' : labels)


locNameFromVal :: Map Val Text -> Val -> Text
locNameFromVal valMap v | v `Map.member` valMap = (valMap ! v) `Text.append` "_"
locNameFromVal _ (ConVal ResetCon)              = "resetCon"
locNameFromVal valMap (TermVal name vs)         = Text.pack $ name ++ "_" ++ List.intercalate "_" (Prelude.map (Text.unpack . locNameFromVal valMap) vs) ++ "_"
locNameFromVal _ (MatchVal _)                   = "matchAbs"
locNameFromVal _ (RecMatchVal x _)              = Text.pack $ "recAbs_" ++ x
locNameFromVal _ (ReceiveVal id)                = Text.pack $ "receiveChEnd_" ++ show id
locNameFromVal _ (SendVal id)                   = Text.pack $ "sendChEnd_" ++ show id
locNameFromVal _ (InPinVal id)                  = Text.pack $ "inPin_" ++ show id
locNameFromVal _ (OutPinVal id)                 = Text.pack $ "outPin_" ++ show id


newLoc :: Text -> TransT Location
newLoc t = do
    locID <- nextLocID
    return $ Location locID [] (Just (t `Text.append` locID)) NormalType


translateStatic :: Val -> TransT Text
translateStatic v = do
    state <- State.get
    case Map.lookup v $ staticMap state of
        Nothing ->
            case v of
                SendVal id    -> updateChannel id
                ReceiveVal id -> updateChannel id
                _             -> liftIO $ print "5" >>  mzero
        Just t  -> return t
    where
        updateChannel :: Integer -> TransT Text
        updateChannel id = do 
            state <- State.get
            let newBindings  = Map.fromList [(SendVal id, Text.pack ("ch" ++ show id)), (ReceiveVal id, Text.pack ("ch" ++ show id))]
            let newStaticMap = staticMap state `Map.union` newBindings
            State.put state{ staticMap = newStaticMap }
            return $ Text.pack ("ch" ++ show id)


translateSync ::  Sync -> TransT Label
translateSync (ReceiveSync (Right ch@(ReceiveVal _)) _) = do 
    channelName <- translateStatic ch
    return $ Label SyncKind $ channelName `Text.append` "?"

translateSync (SendSync (Right ch@(SendVal _)) _ (Just _)) = do 
    channelName <- translateStatic ch
    return $ Label SyncKind $ channelName `Text.append` "!"

translateSync (GetSync (Right pn@(InPinVal _)) b) = do
    pinName <- translateStatic pn
    return $ Label GuardKind $ pinName `Text.append` Text.pack (" == " ++ if b then "1" else "0")

translateSync (SetSync (Right pn@(OutPinVal _)) b) = do
    pinName <- translateStatic pn
    return $ Label AssignmentKind $ pinName `Text.append` Text.pack (" := " ++ if b then "1" else "0")

translateSync _ = liftIO $ print "6" >>  mzero


nextUniqueID :: TransT Integer
nextUniqueID = State.get >>= 
    (\state -> State.put state{ uniqueID = uniqueID state + 1 } >> 
    return (uniqueID state))


nextTempName :: TransT Text
nextTempName = do
    state <- State.get
    State.put state{ tempID = tempID state + 1 }
    return $ Text.pack ("Temp" ++ show (tempID state))


nextLocID :: TransT Text
nextLocID = do
    state <- State.get
    State.put state{ locID = locID state + 1 }
    return $ Text.pack (show (locID state))