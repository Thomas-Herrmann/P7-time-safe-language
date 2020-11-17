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
import Ast
import Partition
import Uppaal

data TransState = TransState {
                               uniqueID  :: Integer
                             , tempID    :: Integer
                             , locID     :: Integer
                             , staticMap :: Map Val Text
                             }

type TransT a = MaybeT (State TransState) a


translate :: Exp -> [Name] -> [Name] -> [Name] -> Name -> Maybe System
translate e clockNames inPinNames outPinNames worldName =
    case runState (runMaybeT (translateExp Map.empty Map.empty [] e')) initState of
        (Nothing, _)              -> Nothing
        (Just (temp, sys), state) -> Just sys{ sysTemplates   = temp : sysTemplates sys, 
                                               sysDecls       = sysDecls sys ++ stateDecls (staticMap state),
                                               sysSystemDecls = makeSysDecls (temp : sysTemplates sys) }
    where
        clocks n     = ClkVal n : clocks (n + 1)
        inPins n     = InPinVal n : inPins (n + 1)
        outPins n    = OutPinVal n : outPins (n + 1)
        clockSubst   = Map.fromList $ Prelude.zip clockNames $ clocks 0
        inPinsSubst  = Map.fromList $ Prelude.zip inPinNames $ inPins 0
        outPinsSubst = Map.fromList $ Prelude.zip outPinNames $ outPins 0
        worldSubst   = Map.singleton worldName WorldVal
        clockMap     = Map.fromList $ Prelude.zip (clocks 0) $ Prelude.map Text.pack clockNames
        inPinMap     = Map.fromList $ Prelude.zip (inPins 0) $ Prelude.map Text.pack inPinNames
        outPinMap    = Map.fromList $ Prelude.zip (outPins 0) $ Prelude.map Text.pack outPinNames
        initState    = TransState 0 0 0 $ clockMap `Map.union` inPinMap `Map.union` outPinMap
        e'           = substitute e $ clockSubst `Map.union` inPinsSubst `Map.union` outPinsSubst `Map.union` worldSubst

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


nilSystem :: Text -> TransT (Template, System)
nilSystem t = do
    name  <- nextTempName
    loc   <- newLoc t
    return (Template name [loc] [] [] (locId loc) (locId loc), System [] [] [] [])


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

translateCtt _ = mzero


simpleMergeSystems :: Text -> (Template, System) -> (Template, System) -> (Template, System)
simpleMergeSystems to (currTemp, currSys) (exisTemp, exisSys) = 
    let newTemp       = exisTemp `joinTemp` currTemp
        newTransition = Transition (temFinal currTemp) to []
    in (newTemp{ temTransitions = newTransition : temTransitions newTemp }, exisSys `joinSys` currSys)


mergeSystems :: Text -> (Template, System) -> (Template, System) -> (Template, System)
mergeSystems from (currTemp, currSys) (exisTemp, exisSys) = 
    let newTemp        = exisTemp `joinTemp` currTemp
        newTransitions = [Transition from (temInit currTemp) [], Transition (temFinal currTemp) (temFinal exisTemp) []]
    in (newTemp{ temTransitions = temTransitions newTemp ++ newTransitions }, exisSys `joinSys` currSys)


translateExp :: Map Name (Text, Text) -> Map Integer (Set Val) -> [([Label], Label)] -> Exp -> TransT (Template, System)
translateExp _ _ _ (ValExp v) = do 
    state <- State.get
    nilSystem $ locNameFromVal (staticMap state) v

translateExp recVars _ _ (RefExp x) | x `Map.member` recVars = do
    (temp, sys) <- nilSystem $ "recRef_" `Text.append` Text.pack x `Text.append` "_"
    locFinal    <- newLoc $ "recRefFinish_" `Text.append` Text.pack x `Text.append` "_"
    let (recInit, recFinish) = recVars ! x
    let recTrans = [Transition (temFinal temp) recInit [], 
                    Transition recFinish (locId locFinal) [], 
                    Transition (locId locFinal) recInit []]
    return (temp{ temLocations   = locFinal : temLocations temp,
                  temFinal       = locId locFinal,
                  temTransitions = temTransitions temp ++ recTrans }, sys)

-- fix has no effect unless applied, as we force it to be wrapped around abstractions!
translateExp _ _ _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) (ValExp (MatchVal _)))))) = nilSystem "fixAbs"

translateExp recVars receivables inVars (AppExp e1 e2) = do
    (temp1, sys1) <- translateExp recVars receivables inVars e1
    (temp2, sys2) <- translateExp recVars receivables inVars e2
    id1           <- nextUniqueID
    case Partition.partition receivables e1 id1 of
        Nothing          -> mzero
        Just (vs1, id1') -> do
            setUniqueID id1'
            id2 <- nextUniqueID
            case Partition.partition receivables e2 id2 of
                Nothing          -> mzero
                Just (vs2, id2') -> do
                    setUniqueID id2'
                    systemSets  <- Prelude.sequence [apply v1 v2 (temFinal temp2) | v1 <- Set.toList vs1, v2 <- Set.toList vs2]
                    let systems = Prelude.foldr Set.union Set.empty systemSets
                    finalLoc    <- newLoc "appDone"
                    let temp3   = (temp1 `joinTemp` temp2){ temFinal = locId finalLoc }
                    let temp3'  = temp3{ temLocations   = finalLoc : temLocations temp3, 
                                          temTransitions = Transition (temFinal temp1) (temInit temp2) [] : temTransitions temp3 }
                    return $ Prelude.foldr (mergeSystems (temFinal temp2)) (temp3', sys1 `joinSys` sys2) systems
    where
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

        apply :: Val -> Val -> Text -> TransT (Set (Template, System)) -- TODO: add RecMatchVal for fix (also in partition)!
        apply (MatchVal body) v2 _ = do
            es      <- matchBody body v2 
            systems <- Prelude.mapM (translateExp recVars receivables inVars) (Set.toList es)
            return $ Set.fromList systems

        apply (RecMatchVal x body) v2 recInit = do
            es           <- matchBody body v2
            finalLoc     <- newLoc "branchFinish"
            let recVars' = Map.insert x (recInit, locId finalLoc) recVars
            systems      <- Prelude.mapM (translateExp recVars' receivables inVars) (Set.toList es)
            let addRecLoc (temp, sys) = (temp{ temFinal = locId finalLoc, temLocations = finalLoc : temLocations temp }, sys)
            let systems' = Prelude.map addRecLoc systems
            return $ Set.fromList systems'

        apply v1@(TermVal _ _) _ _ = do 
            state  <- State.get
            system <- nilSystem $ "app" `Text.append` locNameFromVal (staticMap state) v1
            return $ Set.singleton system

        apply (ConVal ResetCon) v2 _ = do
            (temp, sys) <- nilSystem "appReset"
            finalLoc    <- newLoc "appDone"
            t           <- translateStatic v2
            let label   = Label AssignmentKind $ t `Text.append` " = 0"
            return $ Set.singleton (temp{ temLocations   = finalLoc : temLocations temp,
                                          temTransitions = Transition (temFinal temp) (locId finalLoc) [label] : temTransitions temp,
                                          temFinal       = locId finalLoc }, sys)

        apply (ConVal OpenCon) _ _ = nilSystem "appOpen" <&> Set.singleton

translateExp recVars receivables inVars (InvarExp g _ subst e1 e2) = do
    failLabels    <- translateCtt $ negateCtt g
    [Label _ t]   <- translateCtt g
    locFail       <- newLoc "invarFail"
    locFinish     <- newLoc "invarDone"
    (temp1, sys1) <- translateExp recVars receivables ((failLabels, Label InvariantKind t) : inVars) e1
    let temp1'    = temp1{ temLocations = Prelude.map (addInvariant (Label InvariantKind t)) $ temLocations temp1 }
    let failTrans = [Transition (locId loc) (locId locFail) [failLabel] | loc <- temLocations temp1, failLabel <- failLabels]
    let temp2     = temp1'{ temTransitions = Transition (temFinal temp1') (locId locFinish) [Label GuardKind t] : (temTransitions temp1' ++ failTrans),
                           temLocations   = temLocations temp1' ++ [locFail, locFinish],
                           temFinal       = locId locFinish }
    id2           <- nextUniqueID
    case snapshots receivables subst e1 id2 of
        Nothing             -> mzero
        Just (sigmas, id2') -> do
            setUniqueID id2'
            let e2' = substitute e2 subst
            systems <- Prelude.sequence [translateExp recVars receivables inVars (substitute e2' sigma) | sigma <- Set.toList sigmas]
            return $ Prelude.foldr (mergeSystems (locId locFail)) (temp2, sys1) systems  

translateExp recVars receivables inVars (LetExp x e1 e2) = do
    (temp1, sys1) <- translateExp recVars receivables inVars e1
    id1           <- nextUniqueID
    case Partition.partition receivables e1 id1 of
        Nothing            -> mzero
        Just (vals1, id1') -> do
            setUniqueID id1'
            systems  <- Prelude.sequence [translateExp recVars receivables inVars (substitute e2 (Map.singleton x v)) | v <- Set.toList vals1]
            finalLoc <- newLoc "letDone"
            return $ Prelude.foldr (mergeSystems (temFinal temp1)) (temp1{ temFinal = locId finalLoc, temLocations = finalLoc : temLocations temp1 }, sys1) systems

translateExp recVars receivables inVars (SyncExp body) = do
    (temp, sys) <- nilSystem "syncInit"
    finalLoc    <- newLoc "syncDone"
    systems     <- translateBody (temFinal temp) body
    return $ Prelude.foldr (simpleMergeSystems (locId finalLoc)) (temp{ temFinal = locId finalLoc, temLocations = finalLoc : temLocations temp }, sys) systems
    where
        translateBody from (SingleSync q e)    = translateSyncPair from q e
        translateBody from (MultiSync q e rem) = do 
            systems  <- translateSyncPair from q e
            systems' <- translateBody from rem
            return $ systems ++ systems'

        translateSyncPair from q@(ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            systems     <- Prelude.sequence [translateExp recVars receivables inVars (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            label       <- translateSync q
            let addGuard (temp, sys) = (temp{ temTransitions = Transition from (temInit temp) [label] : temTransitions temp }, sys)
            return $ Prelude.map addGuard systems

        translateSyncPair _ (ReceiveSync (Right (ReceiveVal _)) _) _ = return []

        translateSyncPair from q e = do
            (temp, sys) <- translateExp recVars receivables inVars e
            label       <- translateSync q
            return [(temp{ temTransitions = Transition from (temInit temp) [label] : temTransitions temp }, sys)]


translateExp recVars receivables inVars (GuardExp e g) = do
    guard       <- translateCtt g
    (temp, sys) <- translateExp recVars receivables inVars e
    initLoc     <- newLoc "guardInit"
    let prevInitID = temInit temp
    return (temp{ temLocations   = initLoc : temLocations temp, 
                  temTransitions = Transition (locId initLoc) prevInitID guard : temTransitions temp, 
                  temInit        = locId initLoc }, sys) -- we assume that our guards do not have LOR, although syntactically possible

translateExp _ receivables inVars (ParExp e1 e2) = do
    id <- nextUniqueID
    case multiPassSends e1 e2 2 id of
        Nothing                            -> mzero
        Just (sendables1, sendables2, id') -> do
            setUniqueID id'
            (temp1, sys1)    <- translateExp Map.empty ((receivables `Map.union` sendables2) `Map.difference` sendables1) [] e1
            (temp2, sys2)    <- translateExp Map.empty ((receivables `Map.union` sendables1) `Map.difference` sendables2) [] e2
            (tempMain, sys3) <- nilSystem "parInit"
            let sys4         = sys1 `joinSys` sys2 `joinSys` sys3
            startID          <- nextUniqueID
            stopID1          <- nextUniqueID
            stopID2          <- nextUniqueID
            temp1'           <- addGuards temp1 startID stopID1 inVars
            temp2'           <- addGuards temp2 startID stopID2 inVars
            tempMain'        <- addGuardsMain tempMain startID stopID1 stopID2
            let varDecl      = Text.pack $ "broadcast chan " ++ "start" ++ show startID ++ ";\n chan stop" ++ show stopID1 ++ ", stop" ++ show stopID2 ++ ";\n"
            return (tempMain', sys4{ sysTemplates = sysTemplates sys4 ++ [temp1', temp2'], 
                                     sysDecls = varDecl : sysDecls sys4 })
    where
        varText s id kind = Text.pack $ s ++ show id ++ kind

        addGuards temp startID stopID inVars = do
            initLoc        <- newLoc "init"
            let startLabel = Label SyncKind $ varText "start" startID "?"
            let endLabel   = Label SyncKind $ varText "stop" stopID "!"
            let newTrans   = [Transition (locId initLoc) (temInit temp) [startLabel], Transition (temFinal temp) (locId initLoc) [endLabel]]
            let temp'      = checkInvariant temp (locId initLoc) inVars
            let temp''     = Prelude.foldr (\(_, inVar) temp -> temp{ temLocations = Prelude.map (addInvariant inVar) $ temLocations temp }) temp' inVars
            return $ temp''{ temInit = locId initLoc, 
                           temFinal = locId initLoc, 
                           temLocations = initLoc : temLocations temp'', 
                           temTransitions = temTransitions temp'' ++ newTrans }

        checkInvariant temp to inVars = 
            let failTrans = Prelude.concat [[Transition from to [failLabel] | failLabel <- failLabels, from <- Prelude.map locId $ temLocations temp] | (failLabels, _) <- inVars]
            in  temp{ temTransitions = temTransitions temp ++ failTrans }

        addGuardsMain temp startID stopID1 stopID2 = do
            initLoc        <- newLoc "parInit"
            stopLoc1       <- newLoc "parStopA"
            stopLoc2       <- newLoc "parStopB"
            let startLabel = Label SyncKind $ varText "start" startID "!"
            let endLabel1  = Label SyncKind $ varText "stop" stopID1 "?"
            let endLabel2  = Label SyncKind $ varText "stop" stopID2 "?"
            let newTrans   = [Transition (locId initLoc) (temInit temp) [startLabel], 
                              Transition (temFinal temp) (locId stopLoc1) [endLabel1],
                              Transition (locId stopLoc1) (locId stopLoc2) [endLabel2]]
            return $ temp{ temInit        = locId initLoc,
                           temFinal       = locId stopLoc2,
                           temLocations   = temLocations temp ++ [initLoc, stopLoc1, stopLoc2],
                           temTransitions = temTransitions temp ++ newTrans }

translateExp _ _ _ _ = mzero


addInvariant invar loc =
    let (label, labels) = Prelude.foldr extendInvar (invar, []) $ locLabels loc
    in  loc{ locLabels = label : labels }
    where
        extendInvar (Label InvariantKind t') (Label _ t, labels) = (Label InvariantKind $ t' `Text.append` " and " `Text.append` t, labels)
        extendInvar label' (label, labels)                       = (label, label':labels) 


locNameFromVal :: Map Val Text -> Val -> Text
locNameFromVal valMap v | v `Map.member` valMap = (valMap ! v) `Text.append` "_"
locNameFromVal _ (ConVal ResetCon)              = "resetCon"
locNameFromVal _ (ConVal OpenCon)               = "openCon"
locNameFromVal valMap (TermVal name vs)         = Text.pack $ name ++ "_" ++ List.intercalate "_" (Prelude.map (Text.unpack . locNameFromVal valMap) vs) ++ "_"
locNameFromVal _ (MatchVal _)                   = "matchAbs"
locNameFromVal _ WorldVal                       = "world"


newLoc :: Text -> TransT Location
newLoc t = do
    locID <- nextLocID
    return $ Location locID [] $ Just (t `Text.append` locID)


translateStatic :: Val -> TransT Text
translateStatic v = do
    state <- State.get
    case Map.lookup v $ staticMap state of
        Nothing ->
            case v of
                SendVal id    -> updateChannel id
                ReceiveVal id -> updateChannel id
                _             -> mzero
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

translateSync _ = mzero


nextUniqueID :: TransT Integer
nextUniqueID = State.get >>= 
    (\state -> State.put state{ uniqueID = uniqueID state + 1 } >> 
    return (uniqueID state))


setUniqueID :: Integer -> TransT ()
setUniqueID n = State.get >>=
    (\state -> State.put state{ uniqueID = n })


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