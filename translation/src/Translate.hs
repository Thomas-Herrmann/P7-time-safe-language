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
                               uniqueID :: Integer
                             , tempID   :: Integer
                             , locID    :: Integer
                             , clockMap :: Map Val Text
                             }

type TransT a = MaybeT (State TransState) a


translate :: Exp -> [Name] -> [Name] -> [Name] -> Name -> Maybe System
translate e clockNames inPinNames outPinNames worldName =
    case evalState (runMaybeT (translateExp [] e')) initState of
        Nothing          -> Nothing
        Just (temp, sys) -> Just sys{ sysTemplates = temp:(sysTemplates sys), sysDecls = clockDecl:(sysDecls sys) }
    where
        clocks n     = (ClkVal n):(clocks (n + 1))
        inPins n     = (InPinVal n):(inPins (n + 1))
        outPins n    = (OutPinVal n):(outPins (n + 1))
        clockSubst   = Map.fromList $ Prelude.zip clockNames $ clocks 0
        inPinsSubst  = Map.fromList $ Prelude.zip inPinNames $ inPins 0
        outPinsSubst = Map.fromList $ Prelude.zip outPinNames $ outPins 0
        worldSubst   = Map.singleton worldName WorldVal
        clockDecl    = Text.pack $ "clock " ++ (", " `List.intercalate` clockNames) ++ ";"
        initState    = TransState 0 0 0 $ Map.fromList $ Prelude.zip (clocks 0) $ Prelude.map Text.pack clockNames
        e'           = substitute e $ clockSubst `Map.union` inPinsSubst `Map.union` outPinsSubst `Map.union` worldSubst


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
    return $ Label GuardKind (t1 `Text.append` (Text.pack " and ") `Text.append` t2)

translateCtt (ClockLeqCtt (Right v) n) = 
    translateClock v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" <= " ++ show n)))))

translateCtt (ClockGeqCtt (Right v) n) = 
    translateClock v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" >= " ++ show n)))))

translateCtt (ClockLCtt (Right v) n) = 
    translateClock v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" < " ++ show n)))))

translateCtt (ClockGCtt (Right v) n) = 
    translateClock v >>= 
        (\t -> return (Label GuardKind (t `Text.append` (Text.pack (" > " ++ show n)))))

translateCtt _ = mzero


mergeSystems :: Text -> (Template, System) -> (Template, System) -> (Template, System)
mergeSystems from (currTemp, currSys) (exisTemp, exisSys) = 
    let newTemp        = exisTemp `joinTemp` currTemp
        newTransitions = [Transition from (temInit currTemp) [], Transition (temFinal currTemp) (temFinal exisTemp) []]
    in (newTemp{ temTransitions = temTransitions newTemp ++ newTransitions }, exisSys `joinSys` currSys)


translateExp :: [Text] -> Exp -> TransT (Template, System)
translateExp _ (ValExp _) = nilSystem
translateExp _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = nilSystem

translateExp inVars (AppExp e1 e2) = do
    (temp1, sys1) <- translateExp inVars e1
    (temp2, sys2) <- translateExp inVars e2
    id1           <- nextUniqueID
    case Partition.partition e1 id1 of
        Nothing            -> mzero
        Just (vs1, id1') -> do
            setUniqueID id1'
            id2 <- nextUniqueID
            case Partition.partition e2 id2 of
                Nothing            -> mzero
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
            systems <- Prelude.sequence $ Prelude.map (translateExp inVars) (Set.toList es)
            return $ Set.fromList systems

        apply (TermVal name vs) v2 = nilSystem >>= (\res -> return (Set.singleton res))
        apply (ConVal ResetCon) v2 = do
            (temp, sys) <- nilSystem
            finalLocID  <- nextLocID
            t           <- translateClock v2
            let label   = Label AssignmentKind $ t `Text.append` (Text.pack " = 0")
            return $ Set.singleton (temp{ temLocations   = (Location finalLocID [] $ Just (Text.cons 'L' finalLocID)):(temLocations temp),
                                          temTransitions = (Transition (temFinal temp) finalLocID [label]):(temTransitions temp),
                                          temFinal       = finalLocID }, sys)

        apply (ConVal OpenCon)  v2 = nilSystem >>= (\res -> return (Set.singleton res))

--translateExp inVars (InvarExp g xs _ e1 e2) = do
--  -- TODO!!

translateExp inVars (LetExp x e1 e2) = do
    (temp1, sys1) <- translateExp inVars e1
    id1           <- nextUniqueID
    case Partition.partition e1 id1 of
        Nothing            -> mzero
        Just (vals1, id1') -> do
            setUniqueID id1'
            systems      <- Prelude.sequence [translateExp inVars (substitute e2 (Map.singleton x v)) | v <- Set.toList vals1]   
            finalLocID   <- nextLocID
            let finalLoc = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
            return $ Prelude.foldr (mergeSystems (temFinal temp1)) (temp1{ temFinal = finalLocID, temLocations = finalLoc:(temLocations temp1) }, sys1) systems

translateExp inVars (GuardExp e g) = do
    guard          <- translateCtt g
    (temp, sys)    <- translateExp inVars e
    initLocID      <- nextLocID
    let prevInitID = temInit temp
    let initLoc    = Location initLocID [] $ Just (Text.cons 'L' initLocID)
    return (temp{ temLocations   = initLoc:(temLocations temp), 
                  temTransitions = (Transition initLocID prevInitID [guard]):(temTransitions temp), 
                  temInit        = initLocID }, sys)


translateClock :: Val -> TransT Text
translateClock v = do
    state <- State.get
    case Map.lookup v $ clockMap state of
        Nothing -> mzero
        Just t  -> return t


nextUniqueID :: TransT Integer
nextUniqueID = State.get >>= 
    (\state -> State.put state{ uniqueID = ((uniqueID state) + 1) } >> 
    (return (uniqueID state)))


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