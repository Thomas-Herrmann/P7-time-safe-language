{-# LANGUAGE OverloadedStrings #-}
module Translate
    ( translate
    ) where

import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Control.Monad.Trans.Maybe
import Control.Monad.State as State
import Data.Foldable
import Data.Text as Text
import Ast
import Partition
import Uppaal

data TransState = TransState {
                               uniqueID  :: Integer
                             , tempID    :: Integer
                             , locID     :: Integer
                             , gVarID    :: Integer
                             , staticMap :: Map Val Text
                             }

type TransT a = MaybeT (State TransState) a


translate :: Exp -> [Name] -> [Name] -> [Name] -> Name -> Maybe System
translate e clockNames inPinNames outPinNames worldName =
    case runState (runMaybeT (translateExp Map.empty Map.empty [] e')) initState of
        (Nothing, _)              -> Nothing
        (Just (temp, sys), state) -> Just sys{ sysTemplates   = temp:(sysTemplates sys), 
                                               sysDecls       = sysDecls sys ++ stateDecls (staticMap state),
                                               sysSystemDecls = makeSysDecls (temp:(sysTemplates sys)) }
    where
        clocks n     = (ClkVal n):(clocks (n + 1))
        inPins n     = (InPinVal n):(inPins (n + 1))
        outPins n    = (OutPinVal n):(outPins (n + 1))
        clockSubst   = Map.fromList $ Prelude.zip clockNames $ clocks 0
        inPinsSubst  = Map.fromList $ Prelude.zip inPinNames $ inPins 0
        outPinsSubst = Map.fromList $ Prelude.zip outPinNames $ outPins 0
        worldSubst   = Map.singleton worldName WorldVal
        clockMap     = Map.fromList $ Prelude.zip (clocks 0) $ Prelude.map Text.pack clockNames
        inPinMap     = Map.fromList $ Prelude.zip (inPins 0) $ Prelude.map Text.pack inPinNames
        outPinMap    = Map.fromList $ Prelude.zip (outPins 0) $ Prelude.map Text.pack outPinNames
        initState    = TransState 0 0 0 0 $ clockMap `Map.union` inPinMap `Map.union` outPinMap
        e'           = substitute e $ clockSubst `Map.union` inPinsSubst `Map.union` outPinsSubst `Map.union` worldSubst

        stateDecls :: Map Val Text -> [Declaration]
        stateDecls map = Map.foldrWithKey makeDecl [] map

        makeDecl (ClkVal _) t decls    = ((Text.pack "clock ") `Text.append` t `Text.append` (Text.pack ";\n")):decls
        makeDecl (SendVal _) t decls   = ((Text.pack "chan ") `Text.append` t `Text.append` (Text.pack ";\n")):decls
        makeDecl (InPinVal _) t decls  = ((Text.pack "bool ") `Text.append` t `Text.append` (Text.pack " = 0;\n")):decls
        makeDecl (OutPinVal _) t decls = ((Text.pack "bool ") `Text.append` t `Text.append` (Text.pack " = 0;\n")):decls
        makeDecl _ _ decls             = decls

        makeSysDecls :: [Template] -> [Declaration]
        makeSysDecls temps =
            let tempNames        = Prelude.map temName temps
                foldf name decls = ("P_" `Text.append` name `Text.append` " = " `Text.append` name `Text.append` "();\n"):decls
                tempDecls        = Prelude.foldr foldf [] tempNames
                sysDecl          = "system " `Text.append` (Text.pack (List.intercalate ", " (Prelude.map (((++) "P_") . Text.unpack) tempNames))) `Text.append` ";"
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


nilSystem :: TransT (Template, System)
nilSystem = do
    name  <- nextTempName
    locID <- nextLocID
    let loc = Location locID [] $ Just (Text.cons 'L' locID)
    return (Template name [loc] [] [] locID locID, System [] [] [] [])


translateCtt :: Ctt -> TransT Label
translateCtt (LandCtt g1 g2) = do
    Label _ t1 <- translateCtt g1
    Label _ t2 <- translateCtt g2
    return $ Label GuardKind (t1 `Text.append` " and " `Text.append` t2)

translateCtt (ClockLeqCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" <= " ++ show n)))))

translateCtt (ClockGeqCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" >= " ++ show n)))))

translateCtt (ClockLCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" < " ++ show n)))))

translateCtt (ClockGCtt (Right v) n) = 
    translateStatic v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" > " ++ show n)))))

translateCtt _ = mzero


simpleMergeSystems :: Text -> (Template, System) -> (Template, System) -> (Template, System)
simpleMergeSystems to (currTemp, currSys) (exisTemp, exisSys) = 
    let newTemp       = exisTemp `joinTemp` currTemp
        newTransition = Transition (temFinal currTemp) to []
    in (newTemp{ temTransitions = newTransition:(temTransitions newTemp) }, exisSys `joinSys` currSys)


mergeSystems :: Text -> (Template, System) -> (Template, System) -> (Template, System)
mergeSystems from (currTemp, currSys) (exisTemp, exisSys) = 
    let newTemp        = exisTemp `joinTemp` currTemp
        newTransitions = [Transition from (temInit currTemp) [], Transition (temFinal currTemp) (temFinal exisTemp) []]
    in (newTemp{ temTransitions = temTransitions newTemp ++ newTransitions }, exisSys `joinSys` currSys)


translateExp :: Map Name Text -> Map Integer (Set Val) -> [Text] -> Exp -> TransT (Template, System)
translateExp _ _ _ (ValExp _) = nilSystem

translateExp recVars receivables inVars (FixExp (ValExp (MatchVal (SingleMatch (RefPat x) e)))) = do
    (temp1, sys1) <- nilSystem
    let recVars'  = Map.insert x (temInit temp1) recVars
    (temp2, sys2) <- translateExp recVars' receivables inVars e
    let temp3 = temp1 `joinTemp` temp2
    return (temp3{ temTransitions = (Transition (temFinal temp1) (temInit temp2) []):(temTransitions temp3) }, sys1 `joinSys` sys2)

translateExp recVars receivables inVars (AppExp e1 e2) = do
    (temp1, sys1) <- translateExp recVars receivables inVars e1
    (temp2, sys2) <- translateExp recVars receivables inVars e2
    id1           <- nextUniqueID
    case Partition.partition e1 id1 of
        Nothing          -> mzero
        Just (vs1, id1') -> do
            setUniqueID id1'
            id2 <- nextUniqueID
            case Partition.partition e2 id2 of
                Nothing          -> mzero
                Just (vs2, id2') -> do
                    setUniqueID id2'
                    systemSets   <- Prelude.sequence [apply v1 v2 | v1 <- Set.toList vs1, v2 <- Set.toList vs2]
                    let systems  = Prelude.foldr Set.union Set.empty systemSets
                    finalLocID   <- nextLocID
                    let finalLoc = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
                    let temp3    = (temp1 `joinTemp` temp2){ temFinal = finalLocID }
                    let temp3'   = temp3{ temLocations   = finalLoc:(temLocations temp3), 
                                          temTransitions = (Transition (temFinal temp1) (temInit temp2) []):(temTransitions temp3) }
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

        apply :: Val -> Val -> TransT (Set (Template, System))
        apply (MatchVal body) v2 = do
            es      <- matchBody body v2 
            systems <- Prelude.sequence $ Prelude.map (translateExp recVars receivables inVars) (Set.toList es)
            return $ Set.fromList systems

        apply (TermVal name vs) v2 = nilSystem >>= (\res -> return (Set.singleton res))
        apply (ConVal ResetCon) v2 = do
            (temp, sys) <- nilSystem
            finalLocID  <- nextLocID
            t           <- translateStatic v2
            let label   = Label AssignmentKind $ t `Text.append` " = 0"
            return $ Set.singleton (temp{ temLocations   = (Location finalLocID [] $ Just (Text.cons 'L' finalLocID)):(temLocations temp),
                                          temTransitions = (Transition (temFinal temp) finalLocID [label]):(temTransitions temp),
                                          temFinal       = finalLocID }, sys)

        apply (ConVal OpenCon)  v2 = nilSystem >>= (\res -> return (Set.singleton res))

--translateExp recVars receivables inVars (InvarExp g xs _ e1 e2) = do
--  -- TODO!!

translateExp recVars receivables inVars (LetExp x e1 e2) = do
    (temp1, sys1) <- translateExp recVars receivables inVars e1
    id1           <- nextUniqueID
    case Partition.partition e1 id1 of
        Nothing            -> mzero
        Just (vals1, id1') -> do
            setUniqueID id1'
            systems      <- Prelude.sequence [translateExp recVars receivables inVars (substitute e2 (Map.singleton x v)) | v <- Set.toList vals1]   
            finalLocID   <- nextLocID
            let finalLoc = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
            return $ Prelude.foldr (mergeSystems (temFinal temp1)) (temp1{ temFinal = finalLocID, temLocations = finalLoc:(temLocations temp1) }, sys1) systems

translateExp recVars receivables inVars (SyncExp body) = do
    (temp, sys)  <- nilSystem
    finalLocID   <- nextLocID
    let finalLoc = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
    systems      <- translateBody (temFinal temp) body
    return $ Prelude.foldr (simpleMergeSystems finalLocID) (temp{ temFinal = finalLocID, temLocations = finalLoc:(temLocations temp) }, sys) systems
    where
        translateBody from (SingleSync q e)    = translateSyncPair from q e
        translateBody from (MultiSync q e rem) = do 
            systems  <- translateSyncPair from q e
            systems' <- translateBody from rem
            return $ systems ++ systems'

        translateSyncPair from q@(ReceiveSync (Right ch@(ReceiveVal id)) x) e | id `Map.member` receivables = do
            systems     <- Prelude.sequence [translateExp recVars receivables inVars (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            label       <- translateSync q
            let addGuard (temp, sys) = (temp{ temTransitions = (Transition from (temInit temp) [label]):(temTransitions temp) }, sys)
            return $ Prelude.map addGuard systems

        translateSyncPair from q@(ReceiveSync (Right ch@(ReceiveVal id)) x) e = return []

        translateSyncPair from q e = do
            (temp, sys) <- translateExp recVars receivables inVars e
            label       <- translateSync q
            return $ [(temp{ temTransitions = (Transition from (temInit temp) [label]):(temTransitions temp) }, sys)]


translateExp recVars receivables inVars (GuardExp e g) = do
    guard          <- translateCtt g
    (temp, sys)    <- translateExp recVars receivables inVars e
    initLocID      <- nextLocID
    let prevInitID = temInit temp
    let initLoc    = Location initLocID [] $ Just (Text.cons 'L' initLocID)
    return (temp{ temLocations   = initLoc:(temLocations temp), 
                  temTransitions = (Transition initLocID prevInitID [guard]):(temTransitions temp), 
                  temInit        = initLocID }, sys)

translateExp recVars receivables inVars (ParExp e1 e2) = do
    id1 <- nextUniqueID
    case sends e1 id1 of
        Nothing                 -> mzero
        Just (sendables1, id1') -> do
            setUniqueID id1'
            id2 <- nextUniqueID
            case sends e2 id2 of
                Nothing                 -> mzero
                Just (sendables2, id2') -> do
                    setUniqueID id2'
                    (temp1, sys1)    <- translateExp recVars ((receivables `Map.union` sendables2) `Map.difference` sendables1) inVars e1
                    (temp2, sys2)    <- translateExp recVars ((receivables `Map.union` sendables1) `Map.difference` sendables2) inVars e2
                    (tempMain, sys3) <- nilSystem
                    let sys4         = sys1 `joinSys` sys2 `joinSys` sys3
                    startID          <- nextUniqueID
                    stopID1          <- nextUniqueID
                    stopID2          <- nextUniqueID
                    temp1'           <- addGuards temp1 (varText "start" startID "?") $ varText "stop" stopID1 "!"
                    temp2'           <- addGuards temp2 (varText "start" startID "?") $ varText "stop" stopID2 "!"
                    tempMain''       <- addGuards tempMain (varText "start" startID "!") $ varText "stop" stopID1 "?"
                    finalLocID       <- nextLocID
                    let finalLoc     = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
                    let finalTrans   = Transition (temFinal tempMain'') finalLocID [Label SyncKind (varText "stop" stopID2 "?")]
                    let tempMain'    = tempMain''{ temLocations = finalLoc:(temLocations tempMain''), 
                                                   temTransitions = finalTrans:(temTransitions tempMain''), 
                                                   temFinal = finalLocID }
                    let varDecl      = Text.pack $ "broadcast chan " ++ "start" ++ show startID ++ ";\n chan stop" ++ show stopID1 ++ ", stop" ++ show stopID2 ++ ";\n"
                    return (tempMain', sys4{ sysTemplates = sysTemplates sys4 ++ [temp1', temp2'], 
                                             sysDecls = varDecl:(sysDecls sys4) })
    where
        varText s id kind = Text.pack $ s ++ show id ++ kind

        addGuards temp varStart varStop = do
            initLocID      <- nextLocID
            let initLoc    = Location initLocID [] $ Just (Text.cons 'L' initLocID)
            finalLocID     <- nextLocID
            let finalLoc   = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
            let startLabel = Label SyncKind varStart
            let endLabel   = Label SyncKind varStop
            let newTrans   = [Transition initLocID (temInit temp) [startLabel], Transition (temFinal temp) finalLocID [endLabel]]
            return $ temp{ temInit = initLocID, 
                           temFinal = finalLocID, 
                           temLocations = temLocations temp ++ [initLoc, finalLoc], 
                           temTransitions = temTransitions temp ++ newTrans }

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
translateSync (ReceiveSync (Right ch@(ReceiveVal id)) x) = do 
    channelName <- translateStatic ch
    return $ Label SyncKind $ channelName `Text.append` "?"

translateSync (SendSync (Right ch@(SendVal id)) x (Just v)) = do 
    channelName <- translateStatic ch
    return $ Label SyncKind $ channelName `Text.append` "!"

translateSync (GetSync (Right pn@(InPinVal _)) b) = do
    pinName <- translateStatic pn
    return $ Label GuardKind $ pinName `Text.append` (Text.pack (" == " ++ if b then "1" else "0"))

translateSync (SetSync (Right pn@(OutPinVal _)) b) = do
    pinName <- translateStatic pn
    return $ Label AssignmentKind $ pinName `Text.append` (Text.pack (" := " ++ if b then "1" else "0"))

translateSync _ = mzero


nextUniqueID :: TransT Integer
nextUniqueID = State.get >>= 
    (\state -> State.put state{ uniqueID = ((uniqueID state) + 1) } >> 
    (return (uniqueID state)))


nextVarID :: TransT Integer
nextVarID = State.get >>= 
    (\state -> State.put state{ gVarID = ((gVarID state) + 1) } >> 
    (return (gVarID state)))


setUniqueID :: Integer -> TransT ()
setUniqueID n = State.get >>=
    (\state -> State.put state{ uniqueID = n })


nextTempName :: TransT Text
nextTempName = do
    state <- State.get
    State.put state{ tempID = ((tempID state) + 1) }
    return $ Text.pack ("Temp" ++ show (tempID state))


nextLocID :: TransT Text
nextLocID = do
    state <- State.get
    State.put state{ locID = ((locID state) + 1) }
    return $ Text.pack (show (locID state))