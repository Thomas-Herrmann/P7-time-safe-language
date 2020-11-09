module Translate
    ( translate
    ) where

import Data.Set as Set
import Data.Map as Map
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
                             }

type TransT a = MaybeT (State TransState) a


translate :: Exp -> [Name] -> [Name] -> [Name] -> Name -> Maybe System
translate e clockNames inPinNames outPinNames worldName =
    case evalState (runMaybeT (translateExp [] e')) initState of
        Nothing          -> Nothing
        Just (temp, sys) -> Just sys{ sysTemplates = temp:(sysTemplates sys) }
    where
        initState    = TransState 0 0 0
        clocks n     = (ClkVal n):(clocks (n + 1))
        inPins n     = (InPinVal n):(inPins (n + 1))
        outPins n    = (OutPinVal n):(outPins (n + 1))
        clockSubst   = Map.fromList $ Prelude.zip clockNames $ clocks 0
        inPinsSubst  = Map.fromList $ Prelude.zip inPinNames $ inPins 0
        outPinsSubst = Map.fromList $ Prelude.zip outPinNames $ outPins 0
        worldSubst   = Map.singleton worldName WorldVal
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


translateExp :: [Text] -> Exp -> TransT (Template, System)
translateExp _ (ValExp _) = nilSystem
translateExp _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat _) _)))) = nilSystem

--translateExp inVars (AppExp e1 e2) = do
--    (temp1, sys1)     <- translateExp inVars e1
--    (temp2, sys2)     <- translateExp inVars e2
--    id1               <- nextUniqueID
--    let (vals1, id1') = Partition.partition e1 id1
--    setUniqueID id1'
--    id2               <- nextUniqueID
--    let (vals2, id2') = Partition.partition e2 id2
--    setUniqueID id2'
--    -- TODO: apply!

--translateExp inVars (InvarExp g xs _ e1 e2) = do
--  -- TODO!!

translateExp inVars (LetExp x e1 e2) = do
    (temp1, sys1)     <- translateExp inVars e1
    id1               <- nextUniqueID
    case Partition.partition e1 id1 of
        Nothing            -> mzero
        Just (vals1, id1') -> do
            setUniqueID id1'
            systems           <- Prelude.sequence [translateExp inVars (substitute e2 (Map.singleton x v)) | v <- Set.toList vals1]   
            finalLocID        <- nextLocID
            let finalLoc      = Location finalLocID [] $ Just (Text.cons 'L' finalLocID)
            return $ Prelude.foldr (mergeSystems (temFinal temp1)) (temp1{ temFinal = finalLocID, temLocations = finalLoc:(temLocations temp1) }, sys1) systems
    where
        mergeSystems from (currTemp, currSys) (exisTemp, exisSys) = 
            let newTemp        = exisTemp `joinTemp` currTemp
                newTransitions = [Transition from (temInit currTemp) [], Transition (temFinal currTemp) (temFinal exisTemp) []]
            in (newTemp{ temTransitions = temTransitions newTemp ++ newTransitions }, exisSys `joinSys` currSys)


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