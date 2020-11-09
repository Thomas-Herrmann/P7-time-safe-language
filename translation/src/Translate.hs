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


translateExp :: [Text] -> Exp -> TransT (Template, System)
translateExp inVars (ValExp _) = do 
    name  <- nextTempName
    locID <- nextLocID
    let loc = Location locID [] $ Just locID
    return (Template name [loc] [] [] locID locID, System [] [] [] [])


nextUniqueID :: TransT Integer
nextUniqueID = State.get >>= 
    (\state -> State.put  state{ uniqueID = ((uniqueID state) + 1) } >> 
    (return (uniqueID state)))


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