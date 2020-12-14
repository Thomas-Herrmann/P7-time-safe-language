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

-- Definition of the type saved as state in the Translation monad
data TransState = TransState {
                               shouldPrune :: Bool                     -- Specifies whether the compiler should prune locations
                             , minMaxD     :: Maybe (Integer, Integer) -- Optional min max boundaries to delays in the model
                             , clockDStack :: [Text]                   -- 'stack' of clocks used for 'controlled' delays
                             , uniqueID    :: Integer                  -- The next unique integer ID for arbitrary use
                             , tempID      :: Integer                  -- The next unique integer ID for templates
                             , locID       :: Integer                  -- The next unique integer ID for locations
                             , clockID     :: Integer                  -- The next unique integer ID for clocks used for delays
                             , channelVars :: Map Val Text             -- A map from channel ends to variables used to control delays in synchronizations
                             , failVarLocs :: Map Text [Text]          -- A map from location identifiers to lists of variables that should be reset upon failing from the corresponding location
                             , staticMap   :: Map Val Text             -- A map from statically defined values to their UPPAAL representations
                             }

-- Definition of the translation monad.
-- Provides a simple way to fail a computation using MaybeT,
-- a notion of state through StateT and debugging through IO.
type TransT a = MaybeT (StateT TransState IO) a


-- Simple function used to lift the Maybe monad up to the translation monad
liftMaybe :: Maybe a -> TransT a
liftMaybe = maybe mzero return


-- Implementation of the translation function.
-- Through parameters we specify:
--     1. Whether to prune the generated model
--     2. Optional min max boundaries to delays
--     3. The expression to be translated
--     4. Lists of names for the variables that initially store clocks, in-pins, out-pins and channels (as pairs).
translate :: Bool -> Maybe (Integer, Integer) -> Exp -> [Name] -> [Name] -> [Name] -> [(Name, Name)] -> IO (Maybe System)
translate pruneFlag minMaxD e clockNames inPinNames outPinNames chanNames = do
    maybe <- runStateT (runMaybeT (translateExp Map.empty Map.empty Map.empty [] e' >>= prune)) initState
    case maybe of
        (Nothing, _)                   -> return Nothing -- We could not translate the program, return nothing
        (Just (temp, sys, map), state) -> do             -- We suceeded in translating the program, add a final location 'terminated', and make the necessary declarations
            let finTrans = case minMaxD of
                    Nothing        -> Map.foldr (\set l -> [Transition id "Terminated" [] | id <- Set.toList set] ++ l) [] map
                    Just (minD, _) -> Map.foldr (\set l -> [Transition id "Terminated" (termDLabels minD) | id <- Set.toList set] ++ l) [] map
            let temp'    = temp{  temLocations   = Location "Terminated"  [] (Just "Terminated") NormalType : temLocations temp,
                                  temTransitions = Transition "Terminated" "Terminated" [] : temTransitions temp ++ finTrans }
            return $ Just sys{ sysTemplates   = temp' : sysTemplates sys, 
                               sysDecls       = "clock clkD1;\n" : sysDecls sys ++ stateDecls (staticMap state) ++ syncVarDecls (channelVars state),
                               sysSystemDecls = makeSysDecls (temp : sysTemplates sys) }
    where
        -- Make the initial state; Make all the necessary clocks, pins and channels
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
        initState      = TransState pruneFlag minMaxD ["clkD1"] 0 0 0 2 Map.empty Map.empty $ clockMap `Map.union` inPinMap `Map.union` outPinMap
        e'             = substitute e $ clockSubst `Map.union` inPinsSubst `Map.union` outPinsSubst `Map.union` chanSubst

        -- Makes labels for edges that constraint delays
        termDLabels min = [Label GuardKind ("clkD1 >= " `Text.append` Text.pack (show min)), Label AssignmentKind "clkD1 := 0"]

        -- Functions used to make declarations of clocks etc.
        stateDecls :: Map Val Text -> [Declaration]
        stateDecls map = Map.foldrWithKey makeDecl [] map
            where
                makeDecl (ClkVal _) t decls    = ("clock " `Text.append` t `Text.append` ";\n") : decls
                makeDecl (SendVal _) t decls   = ("chan " `Text.append` t `Text.append` ";\n") : decls
                makeDecl (InPinVal _) t decls  = ("bool " `Text.append` t `Text.append` " = 0;\n") : decls
                makeDecl (OutPinVal _) t decls = ("bool " `Text.append` t `Text.append` " = 0;\n") : decls
                makeDecl _ _ decls             = decls

        syncVarDecls :: Map Val Text -> [Declaration]
        syncVarDecls map = Map.foldrWithKey makeDecl [] map
            where
                makeDecl _ t decls    = ("bool " `Text.append` t `Text.append` " = 0;\n") : decls

        makeSysDecls :: [Template] -> [Declaration]
        makeSysDecls temps =
            let tempNames        = Prelude.map temName temps
                foldf name decls = ("P_" `Text.append` name `Text.append` " = " `Text.append` name `Text.append` "();\n"):decls
                tempDecls        = Prelude.foldr foldf [] tempNames
                sysDecl          = "system " `Text.append` Text.pack (List.intercalate ", " (Prelude.map ((++) "P_" . Text.unpack) tempNames)) `Text.append` ";"
            in tempDecls ++ [sysDecl]


-- Joins two systems, by appending their lists of declarations, templates etc.
joinSys :: System -> System -> System
sys1 `joinSys` sys2 = sys1{ 
    sysDecls       = sysDecls sys1 ++ sysDecls sys2,
    sysTemplates   = sysTemplates sys1 ++ sysTemplates sys2,
    sysSystemDecls = sysSystemDecls sys1 ++ sysSystemDecls sys2,
    sysQueries     = sysQueries sys1 ++ sysQueries sys2
 }


-- Joins two templates, by appending their lists of locations, transitions etc.
-- The first specified template keeps its initial location.
joinTemp :: Template -> Template -> Template
temp1 `joinTemp` temp2 = temp1{
    temLocations   = temLocations temp1 ++ temLocations temp2,
    temTransitions = temTransitions temp1 ++ temTransitions temp2,
    temDecls       = temDecls temp1 ++ temDecls temp2
}


joinLabel :: Label -> Label -> [Label]
joinLabel (Label GuardKind t1) (Label GuardKind t2)           = [Label GuardKind $ t1 `Text.append` "and " `Text.append` t2]
joinLabel (Label AssignmentKind t1) (Label AssignmentKind t2) = [Label AssignmentKind $ t1 `Text.append` ", " `Text.append` t2]
joinLabel (Label InvariantKind t1) (Label InvariantKind t2)   = [Label InvariantKind $ t1 `Text.append` " and " `Text.append` t2]
joinLabel (Label SyncKind _) (Label SyncKind _)               = error "not defined"
joinLabel l1 l2                                               = [l1, l2]


-- Generates a new clock for specifying constraints to delays,
-- and puts it on the stack of such clocks in the translation state.
putClkD :: TransT Text
putClkD = do
    state    <- State.get
    let name = "clkD" `Text.append` Text.pack (show (clockID state))
    put state{ clockDStack = name : clockDStack state, clockID = 1 + clockID state }
    return $ "clock " `Text.append` name `Text.append` ";\n"


-- Pops the top-most clock from the stack of clocks used for specifying constraints to delays in the translation state
popClkD :: TransT ()
popClkD = do
    state <- State.get
    let _:clks = clockDStack state
    put state{ clockDStack = clks }


-- Maps the specified list of transitions,
-- such that each transition has two new labels; 1 for guarding the minimum delay; 1 for resetting the 'delay' clock.
-- In case any transition already has guards or assignments, we append to the existing labels.
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


-- Same effect as 'addMinMaxEdge', except we only add a label to reset the 'delay' clock.
-- We use this function on transitions with synchronizations,
-- as we cannot constraint the delays here (they depend on other synchronization expressions).
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


-- Maps the specified list of locations,
-- such that each location is given a new invariant that provides an upper bound to delays in each location.
-- In case any location already has an invariant, we 'and' the existing and new invariants.
addMinMaxLoc :: [Location] -> TransT [Location]
addMinMaxLoc locs = do
    state <- State.get
    let clk:_ = clockDStack state
    minMaxD <- State.get <&> minMaxD
    return $ case minMaxD of
        Nothing        -> locs
        Just (_, maxD) -> Prelude.map (addInvariant $ Label InvariantKind $ clk `Text.append` " <= " `Text.append` Text.pack (show maxD)) locs


-- Prunes locations in the template of the specified triple,
-- if 'shouldPrune' is true in the translation state.
prune :: (Template, System, Map Val (Set Text)) -> TransT (Template, System, Map Val (Set Text))
prune (temp, sys, map) = do
    state <- State.get
    let clk:_ = clockDStack state
    if shouldPrune state
        then return (pruneTemplate clk temp, sys, map)
        else return (temp, sys, map) -- Do no pruning


-- Returns a pair of a new template and system,
-- such that:
--     1. The template has a single location with a name based on the specified Text
--     2. The system is 'empty'
--     3. We constraint delays in the template, if such constraints are specified in the translation state
nilSystem :: Text -> TransT (Template, System)
nilSystem t = do
    name <- nextTempName
    loc  <- newLoc t
    locs <- addMinMaxLoc [loc]
    return (Template name locs [] [] (locId loc) (locId loc), System [] [] [] [])


-- Transforms the specified temporal constraint,
-- such that it is slightly more 'forgiving' for use in UPPAAL invariants.
-- Refer to the specification for a definition of the transformation.
cttToInvariant :: Ctt -> Ctt
cttToInvariant (LandCtt g1 g2)   = LandCtt (cttToInvariant g1) (cttToInvariant g2)
cttToInvariant (ClockLeqCtt x n) = ClockLeqCtt x $ n + 1
cttToInvariant (ClockGeqCtt x n) = ClockGeqCtt x $ n - 1
cttToInvariant (ClockLCtt x n)   = ClockLeqCtt x n
cttToInvariant (ClockGCtt x n)   = ClockGeqCtt x n
cttToInvariant (LorCtt _ _)      = error "Logical OR may only be used on fail edges!"


-- Translates the specified temporal constraint to a list of labels.
-- Note that negation may introduce logical ORs, which are not support by UPPAAL.
-- In such cases, we much specify multiple transitions, thereby simulating the logical OR.
-- Therefore, we return a list of Labels, although it has cardinality 1 in most cases.
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


-- Implementation of the translation rules from expressions to UPPAAL models.
-- We specify:
--     1. A substitution, mapping references to recursive functions to their corresponding function bodies
--     2. A map from references to recursive functions to pairs of corresponding location identifiers for 'recInit' and 'recFinish' locations
--     3. A map from channel identifiers to sets of possible values to be received on the corresponding channels
--     4. A list of pairs of a list of 'fail labels' and a single 'invariant label' used for adding 'fail transitions' to new templates created from parallel compositions. 
--        We require a list of fail cases to simulate logical ORs from negation of our temporal constraints.
--     5. The expression to be translated
-- We return a triple consisting of:
--     1. The 'main' template, corresponding to the template of the expression's root node
--     2. A system containing all other templates created from parallel compositions, as well as global declarations
--     3. A map from values to sets of locations, marking the end locations of the constructed model, while mapping them to values
translateExp :: Subst -> Map Name (Text, Text) -> Map Integer (Set Val) -> [([Label], Label)] -> Exp -> TransT (Template, System, Map Val (Set Text))

-- values are simply represented by a single location,
-- marked with the value name.
translateExp _ _ _ _ (ValExp v) = do 
    state       <- State.get
    (temp, sys) <- nilSystem $ locNameFromVal (staticMap state) v
    return (temp, sys, Map.singleton v $ Set.singleton (temInit temp))

-- fix has no effect unless applied, as we force it to be wrapped around abstractions!
-- Therefore, we simply represent it by a single location.
translateExp _ _ _ _ (FixExp (ValExp (MatchVal (SingleMatch (RefPat x) (ValExp (MatchVal body)))))) = do 
    (temp, sys) <- nilSystem "fixAbs"
    return (temp, sys, Map.singleton (RecMatchVal x body) $ Set.singleton (temInit temp))

-- a reference to variable x is only valid,
-- if we are currently translating the body of a recursive function of name x,
-- and the reference acts as function in an application, denoting a recursive call.
-- If this is the case, we introduce two locations:
--     1. one to represent the recursive call.
--     2. one to represent returning from the recursive call.
-- We then introduce transitions from location 1 to the initial location of the function,
-- and to location 2 from the final location of the function.
translateExp recSubst recVars receivables inVars (AppExp (RefExp x) e2) | x `Map.notMember` recSubst = mzero
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

-- for function applications, we first translate e1 and e2 in 'sequence'.
-- We introduce variables that signify which value each expression results in.
-- For each possible combination of v1 and v2 from e1 and e2, 
-- we translate the body of v1 with v2 as argument, and branch based on the variables.
-- The model constructed for each combination depends on the type of function v1 is.
translateExp recSubst recVars receivables inVars (AppExp e1 e2) = do
    (temp1, sys1, map1) <- translateExp recSubst recVars receivables inVars e1
    (temp2, sys2, map2) <- translateExp recSubst recVars receivables inVars e2
    let vs1             = Map.keys map1
    let vs2             = Map.keys map2
    branchLoc           <- newLoc "branch"
    bJoinLoc            <- newLoc "branchJoin"
    mappedLocs          <- addMinMaxLoc [branchLoc, bJoinLoc]
    case () of
        -- we introduce 'branching' labels to transitions, as there are more than one combination of v1 and v2
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
          -- there is at most one combination of v1 and v2, so we do not need 'brancing' labels on transitions
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

        -- finds the branch expressions of a matchbody, when matched with value v
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

        -- builds the models of the possible expressions that may follow from a combination of values,
        -- from two expressions in a function application.
        -- There is exactly one such system for the RESET constant and for termconstructors,
        -- but there may be multiple from abstractions, in case multiple patterns match.
        apply :: Val -> Val -> Text -> Text -> TransT (Set (Template, System, Map Val (Set Text)))

        -- non recursive abstraction, return the translations of the branches that match v2
        apply (MatchVal body) v2 _ _ = do
            es      <- matchBody body v2
            systems <- Prelude.mapM (translateExp recSubst recVars receivables inVars) (Set.toList es)
            return $ Set.fromList systems

        -- recursive abstraction, return the translations of the branches that match v2.
        -- We update the recVars and recSubst arguments when translating the branches,
        -- to correctly build the structure of a model representing a recursive function.
        -- While the model representing an abstraction may have multiple final locations,
        -- we introduce transitions to ensure exactly one such location,
        -- such that all of the function branches have a transition to each location representing returning from recursive calls.
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

        -- for termconstructors, simply introduce a single location,
        -- representing the value of the termconstructor applied to v2.
        apply v1@(TermVal name vs) v2 _ _ = do 
            state  <- State.get
            (temp, sys) <- nilSystem $ "app" `Text.append` locNameFromVal (staticMap state) v1
            return $ Set.singleton (temp, sys, Map.singleton (TermVal name $ vs ++ [v2]) (Set.singleton (temInit temp)))

        -- for the RESET constant, introduce two locations with a transition inbetween,
        -- for which a label is introduced that resets v2.
        -- This only works if v2 is actually a clock.
        -- The second location is the final location, which represents the value v2,
        -- thereby maintaining uniqueness typing.
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

-- for invariants, we first translate e1.
-- For each location and transition of this model, we introduce uppaal invariants and guards, respectively.
-- These are based upon g, as described in the article.
-- Similarly, we introduce a transition from each such location to a new intermediate location, representing failing.
-- Then, for each possible substitution sigma, with regards to the variables that may be sent/received in the invariant body,
-- we translate e2 with sigma applied to it.
-- To the initial location of each such translation of e2, we introduce transition from the intermediate fail location.
-- The final locations of the complete invariant model is then all final locations of e1 and of each model for e2.
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
    failVarLocs   <- State.get <&> failVarLocs
    failTrans     <- addClockDResetEdge [Transition (locId loc) (locId locFail) ([failLabel] ++ (resetVarsLabel failVarLocs (locId loc))) | loc <- locInit : temLocations temp1, failLabel <- failLabels]
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

        resetVarsLabel map locId | locId `Map.member` map = [Label AssignmentKind $ Text.intercalate ", " $ Prelude.map (`Text.append` ":= 0") $ map ! locId]
                                 | otherwise              = []

        makePair guard prevMap (map, ts, ls) v = do
            state     <- State.get
            loc       <- newLoc $ "invarSucc_" `Text.append` locNameFromVal (staticMap state) v
            mappedLoc <- addMinMaxLoc [loc]
            ts'       <- addMinMaxEdge [Transition id (locId loc) [guard] | id <- Set.toList $ prevMap ! v]
            return (Map.unionWith Set.union (Map.singleton v (Set.singleton (locId loc))) map, ts' ++ ts, mappedLoc ++ ls)

-- for let-expressions, let x = e1 in e2, we first translate e1.
-- Then for each final location marked with some variable v,
-- we translate e2 with x substituted for v.
-- We introduce a transition between the corresponding final location of e1 and the initial location of the specific e2 translation.
translateExp recSubst recVars receivables inVars (LetExp x e1 e2) = do
    (temp1, sys1, map1) <- translateExp recSubst recVars receivables inVars e1
    let vs1             = Map.keys map1
    systems             <- Prelude.sequence [addTransitions map1 v $ translateExp recSubst recVars receivables inVars (substitute e2 (Map.singleton x v)) | v <- vs1]
    prune $ Prelude.foldr joinTuples (temp1, sys1, Map.empty) systems
    where
        joinTuples (t1, s1, m1) (t2, s2, m2) = (t2 `joinTemp` t1, s2 `joinSys` s1, m2 `Map.union` m1)

        addTransitions :: Map Val (Set Text) -> Val -> TransT (Template, System, Map Val (Set Text)) -> TransT (Template, System, Map Val (Set Text))
        addTransitions map v monad | v `Map.notMember` map = mzero
                                   | otherwise             = do
            (temp, sys, map') <- monad
            newTrans          <- addMinMaxEdge [Transition id (temInit temp) [] | id <- Set.toList $ map ! v]
            return (temp{ temTransitions = newTrans ++ temTransitions temp }, sys, map')

-- for synchronization expressions, we first introduce two new locations.
-- We add a transition between these, that assigns true to the variables, 
-- representing the action we want to do on the channels we synchronize on in the synchronization expression.
-- We then translate the body of the synchronization expression.
-- In case we want to constraint delays, we introduce invariants on the locations and transitions,
-- such that we are forced to synchronize once some other synchronization expression is ready to synchronize with us.
-- We accomplish this by guarding on the values of the variables corresponding to the dual of the variables we assigned to previously.
-- Upon synchronization, we reset the values of these variables, signifying we are no longer ready to synchronize.
translateExp recSubst recVars receivables inVars (SyncExp body) = do
    (temp, sys)     <- nilSystem "syncInit"
    (sVars, mRVars) <- findChannelVars body
    pVars           <- findPinVars body
    waitLoc         <- newLoc "syncWait"
    State.get >>= \state -> State.put state{ failVarLocs = Map.insert (locId waitLoc) sVars (failVarLocs state) } -- if we enter the fail case of an invariant from this location, we must reset all sVars!
    mappedLoc       <- addMinMaxLoc [waitLoc]
    varSetTrans     <- addMinMaxEdge $ 
        if Prelude.null sVars
            then [Transition (temInit temp) (locId waitLoc) []] 
            else [Transition (temInit temp) (locId waitLoc) [Label AssignmentKind $ Text.intercalate ", " $ Prelude.map (`Text.append` " := 1") sVars]]
    systems         <- translateBody (locId waitLoc) sVars body
    minMaxD         <- State.get <&> minMaxD
    resetTrans      <- case (minMaxD, mRVars) of
            (Nothing, _)    -> return []
            (_, Nothing)    -> return []
            (_, Just rVars) -> do 
                let guard1 = Label GuardKind $ Text.intercalate " and " $ Prelude.map (`Text.append` " == 0") rVars
                let guard2 = Label GuardKind $ Text.intercalate " and " pVars
                let guards = 
                        case () of
                            _ | Prelude.null rVars && Prelude.null pVars -> []
                              | Prelude.null rVars                       -> [guard2]
                              | Prelude.null pVars                       -> [guard1]
                              | otherwise                                -> guard1 `joinLabel` guard2
                addMinMaxEdge [Transition (locId waitLoc) (locId waitLoc) guards]
    prune $ Prelude.foldr joinTuples (temp{ temLocations   = mappedLoc ++ temLocations temp, 
                                            temTransitions = varSetTrans ++ resetTrans ++ temTransitions temp}, sys, Map.empty) systems
    where
        joinTuples (t1, s1, m1) (t2, s2, m2) = (t2 `joinTemp` t1, s2 `joinSys` s1, m2 `Map.union` m1)

        findPinVars (SingleSync q _)    = findSyncPinVars q 
        findPinVars (MultiSync q _ rem) = do
            vars  <- findSyncPinVars q
            vars' <- findPinVars rem
            return $ vars ++ vars'

        -- finds the uppaal representations of 'guarding on the value of a pin'.
        -- For instance, if we want to sync on "pin1 == 1",
        -- we need the dual "pin1 == 0" as a guard on the transition resetting the clock for delay constraints,
        -- such that we may reset the clock until the pin has the value we want.
        findSyncPinVars :: Sync -> TransT [Text]
        findSyncPinVars (GetSync (Right v@(InPinVal _)) b) = do
            staticMap <- State.get <&> staticMap
            case Map.lookup v staticMap of
                Nothing -> mzero
                Just t  -> do 
                    let bText = if not b then "1" else "0"
                    return [t `Text.append` " == " `Text.append` bText]

        findSyncPinVars _ = return []
        
        -- finds a series of uppaal representations of variables, 
        -- representing the synchronizations we want to do on channels in the specified synchronization body.
        findChannelVars :: SyncBody -> TransT ([Text], Maybe [Text])
        findChannelVars (SingleSync q _) = do
            maybePair <- findSyncVar q
            return $ case maybePair of
                Nothing           -> ([], Nothing)
                Just (sVar, rVar) -> (sVar, Just rVar)

        findChannelVars (MultiSync q _ rem) = do
            maybePair           <- findSyncVar q
            (sVars, maybeRVars) <- findChannelVars rem
            return $ case (maybePair, maybeRVars) of
                (Nothing, _)                    -> (sVars, Nothing)
                (Just (sVar, rVar), Nothing)    -> (sVar ++ sVars, Nothing)
                (Just (sVar, rVar), Just rVars) -> (sVar ++ sVars, Just $ rVar ++ rVars)

        findSyncVar :: Sync -> TransT (Maybe ([Text], [Text]))
        findSyncVar (ReceiveSync (Right (ReceiveVal id)) _) = do
            translateStatic $ ReceiveVal id -- ensure a variable exists for the channel end
            state <- State.get <&> channelVars 
            return $ Just ([state ! ReceiveVal id], [state ! SendVal id]) 

        findSyncVar (SendSync (Right (SendVal id)) _ _) = do
            translateStatic $ SendVal id -- ensure a variable exists for the channel end
            state <- State.get <&> channelVars
            return $ Just ([state ! SendVal id], [state ! ReceiveVal id])

        findSyncVar (GetSync (Right (InPinVal _)) _)  = return $ Just ([], [])
        findSyncVar (SetSync (Right (OutPinVal _)) _) = return Nothing
        findSyncVar _                                 = mzero

        -- returns a list containing models for the branches of a synchronization expression body.
        translateBody from sVars (SingleSync q e)    = translateSyncPair from sVars q e
        translateBody from sVars (MultiSync q e rem) = do 
            systems  <- translateSyncPair from sVars q e
            systems' <- translateBody from sVars rem
            return $ systems ++ systems'

        -- returns a list containing models for the possible models for some synchronization and corresponding expression.
        -- There may only be multiple models for receiving synchronizations,
        -- as we may receive one of multiple values. 
        translateSyncPair from sVars q@(ReceiveSync (Right (ReceiveVal id)) x) e | id `Map.member` receivables = do
            systems                       <- Prelude.sequence [translateExp recSubst recVars receivables inVars (substitute e (Map.singleton x v)) | v <- Set.toList (receivables ! id)]
            label                         <- translateSync q
            let labels                    =
                    if Prelude.null sVars
                        then [label]
                        else joinLabel label $ Label AssignmentKind $ Text.intercalate ", " $ Prelude.map (`Text.append` " := 0") sVars
            let addGuard (temp, sys, map) = do
                    link <- addClockDResetEdge [Transition from (temInit temp) labels]
                    return (temp{ temTransitions = link ++ temTransitions temp }, sys, map)
            Prelude.mapM addGuard systems

        translateSyncPair _ _ (ReceiveSync (Right (ReceiveVal _)) _) _ = return []

        translateSyncPair from sVars q e = do
            (temp, sys, map) <- translateExp recSubst recVars receivables inVars e
            label            <- translateSync q
            let labels =
                    if Prelude.null sVars
                        then [label]
                        else joinLabel label $ Label AssignmentKind $ Text.intercalate ", " $ Prelude.map (`Text.append` " := 0") sVars
            link             <- addClockDResetEdge [Transition from (temInit temp) labels]
            return [(temp{ temTransitions = link ++ temTransitions temp }, sys, map)]

-- for guarded expressions, we introduce two new locations,
-- for which we add a transition between guarded by the uppaal equivalent of the guard.
-- We then translate the expression, and add a transition between the second location and the initial location of the expression,
-- labelled with the same guard.
-- On the second location, we introduce an uppaal invariant that holds while the guard can still be satisfied at some point.
-- Thus, once we enter the second location, we are forced to continue with the expression, before the guard can no longer be satisfied.
-- In case we want to constraint the delay from the first location to the second,
-- we introduce a uppaal invariant on the first location based upon the maximum delay constraint.
-- We then add a transition that resets the clock used for constrainting delays in this template,
-- but that is guarded by the guard not holdning.
-- Thus, we are forced to enter the second location before max delay after the guard is satisfied.
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
                _       -> do 
                    negGuardLabels <- translateCtt $ negateCtt g
                    addMinMaxEdge [Transition (locId initLoc) (locId initLoc) [label] | label <- negGuardLabels]
    interLoc         <- newLoc "guardSatisfied" <&> \loc -> loc{ locLabels = [Label InvariantKind invar] }
    let initTrans    = Transition (locId initLoc) (locId interLoc) guard
    guardBreakTrans  <- addClockDResetEdge [Transition (locId interLoc) (temInit temp) guard]
    prune (temp{ temLocations   = interLoc : (mappedLoc ++ temLocations temp), 
                 temTransitions = clockResetTrans ++ [initTrans] ++ guardBreakTrans ++ temTransitions temp, 
                 temInit        = locId initLoc }, sys, map) -- we assume that our guards do not have LOR, although syntactically possible

-- for parallel compositions, we introduce two additional templates,
-- corresponding to the subexpressions e1 and e2 translated.
-- We use the original/root template to 'control' the templates for e1 and e2,
-- by introducing synchronizations, such that the original template broadcasts to e1 and e2 when they should initiate.
-- Similarly, e1 and e2 synchronize with the original template one at a time, to signify that they have finished.
-- Once both e1 and e2 have finished, they return to their initial states to be reused,
-- and the original template transitions to one of its final locations, based on the combination of values from e1 and e2.
-- These final locations represent pair values.
-- We control the branching to final locations based on global variables, one for e1 and one for e2, 
-- such that the templates for these assign to their corresponding variable which value they ended up with.
-- This way, we do not lose information in parallel compositions, although we have multiple templates.
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
    let varDecl''            = Text.pack ("bool readyStart" ++ show startID ++ " := 0; bool readyStop" ++ show stopID1 ++ " := 0; bool readyStop" ++ show stopID2 ++ ";\n") `Text.append` varDecl'
    prune (tempMain', sys4{ sysTemplates = sysTemplates sys4 ++ [temp1', temp2'], 
                            sysDecls = clockDecl1 : clockDecl2 : varDecl'' : sysDecls sys4 }, mapRes)
    where
        varText s id kind = Text.pack $ s ++ show id ++ kind

        -- auxiliary function used to build a map from values to integers and a new uppaal variable,
        -- such that we can represent values in our language by distinct integer values in uppaal, 
        -- and thereby share information between templates.
        setUpVarBranch :: Map Val (Set Text) -> TransT (Map Val Integer, Text)
        setUpVarBranch map = do
            let (intValMap, _) = Map.foldrWithKey (\v _ (map, n) -> (Map.insert v n map, n + 1)) (Map.empty, 0) map
            varId              <- nextUniqueID
            let varName        = "selector" `Text.append` Text.pack (show varId)
            return (intValMap, varName)

        -- auxiliary function that introduces synchronizations to the subexpression of a parallel composition,
        -- such that it can communicate with the original/root template about when to start and stop.
        addGuards temp intMap locMap var startID stopID inVars = do
            hasMinMaxD      <- getHasMinMaxD
            let forceDLabel = [Label AssignmentKind $ Text.pack $ "readyStop" ++ show stopID ++ " := 1" | hasMinMaxD ]
            initLoc         <- newLoc "init"
            varLoc          <- newLoc "varSet"
            mappedLoc       <- addMinMaxLoc [initLoc, varLoc]
            waitStartTrans  <- makeDelayTrans hasMinMaxD (locId initLoc)
            let vs          = Map.keys locMap
            let startLabel  = Label SyncKind $ varText "start" startID "?"
            let endLabel    = Label SyncKind $ varText "stop" stopID "!"
            let varLabel v  = Label AssignmentKind $ var `Text.append` Text.pack (" := " ++ show (intMap ! v) ++ if hasMinMaxD then ", readyStop" ++ show stopID ++ " := 0" else "")
            let foldf v l   = Prelude.concat [[Transition id (locId varLoc) forceDLabel, Transition (locId varLoc) (locId initLoc) [endLabel, varLabel v]] | id <- Set.toList $ locMap ! v] ++ l
            newTrans        <- addClockDResetEdge $ Transition (locId initLoc) (temInit temp) [startLabel] : Prelude.foldr foldf [] vs
            temp'           <- checkInvariant temp (locId initLoc) inVars
            let temp''      = Prelude.foldr (\(_, inVar) temp -> temp{ temLocations = Prelude.map (addInvariant inVar) $ temLocations temp }) temp' inVars
            return $ temp''{ temInit        = locId initLoc,
                             temLocations   = mappedLoc ++ temLocations temp'', 
                             temTransitions = temTransitions temp'' ++ newTrans ++ waitStartTrans }
            where
                makeDelayTrans b id = 
                    if b 
                        then addMinMaxEdge [Transition id id [Label GuardKind $ Text.pack $ "readyStart" ++ show startID ++ " == 0"]]
                        else return []

        -- auxiliary function used when a parallel composition is within an invariant body,
        -- such that we must introduce fail-transitions for when the invariant fails.
        checkInvariant temp to inVars = do
            failTrans <- addClockDResetEdge $ Prelude.concat [[Transition from to [failLabel] | failLabel <- failLabels, from <- Prelude.map locId $ temLocations temp] | (failLabels, _) <- inVars]
            return temp{ temTransitions = temTransitions temp ++ failTrans }

        -- used to convieniently check whether we want to constraint delays in the transition (optional)
        getHasMinMaxD = do
            minMaxD        <- State.get <&> minMaxD
            return $ case minMaxD of
                Nothing -> False
                Just _  -> True

        -- similar to addGuards, but for the original/root template.
        -- Introduces synchronizations to the template,
        -- such that it can broadcast to the subexpression templates when to start,
        -- and so that it can wait for the subexpressions to finish, before continuing.
        addGuardsMain temp intValMap1 var1 intValMap2 var2 startID stopID1 stopID2 = do
            hasMinMaxD             <- getHasMinMaxD
            initLoc                <- newLoc "parStart"
            waitLoc                <- newLoc "parVarSet"
            stopLoc1               <- newLoc "parStopA"
            stopLoc2               <- newLoc "parStopB"
            let updateLabels       = [Label AssignmentKind $ Text.pack $ "readyStart" ++ show startID ++ " := 1" | hasMinMaxD]
            let startLabel         = Label SyncKind $ varText "start" startID "!"
            let endLabel1          = Label SyncKind $ varText "stop" stopID1 "?"
            let endLabel2          = Label SyncKind $ varText "stop" stopID2 "?"
            let varLabel = Label AssignmentKind $ Text.pack $ "readyStart" ++ show startID ++ " := 0"
            let vs1                = Map.keys intValMap1
            let vs2                = Map.keys intValMap2
            branchPairs            <- Prelude.sequence [makePair (locId stopLoc2) v1 v2 | v1 <- vs1, v2 <- vs2]
            let newLocs            = Prelude.map (snd . fst) branchPairs
            mappedLocs             <- addMinMaxLoc $ waitLoc : initLoc : stopLoc1 : stopLoc2 : newLocs
            delayTrans             <- makeDelayTrans hasMinMaxD (locId waitLoc) (locId stopLoc1)
            let (locMap, newTrans) = Prelude.foldr (\((v, loc), t) (map, ts) -> (Map.insert v (Set.singleton (locId loc)) map, t : ts)) (Map.empty, []) branchPairs
            mappedTrans            <- addClockDResetEdge newTrans
            let newTrans'          = Transition (temInit temp) (locId initLoc) updateLabels   : 
                                     Transition (locId initLoc) (locId waitLoc) [startLabel]  : 
                                     Transition (locId waitLoc) (locId stopLoc1) [endLabel1, varLabel]  :
                                     Transition (locId waitLoc) (locId stopLoc1) [endLabel2, varLabel]  :
                                     Transition (locId stopLoc1) (locId stopLoc2) [endLabel1] :
                                     Transition (locId stopLoc1) (locId stopLoc2) [endLabel2] : mappedTrans
            return (temp{ temInit        = temInit temp,
                          temLocations   = temLocations temp ++ mappedLocs,
                          temTransitions = temTransitions temp ++ newTrans' ++ delayTrans }, locMap)
            where
                makeDelayTrans b id1 id2 = 
                    if b 
                        then addMinMaxEdge [Transition id1 id1 [Label GuardKind $ Text.pack $ "readyStop" ++ show stopID1 ++ " == 0 and readyStop" ++ show stopID2 ++ " == 0"], 
                                                 Transition id2 id2 [Label GuardKind $ Text.pack $ "readyStop" ++ show stopID1 ++ " == 0 and readyStop" ++ show stopID2 ++ " == 1"],
                                                 Transition id2 id2 [Label GuardKind $ Text.pack $ "readyStop" ++ show stopID2 ++ " == 0 and readyStop" ++ show stopID1 ++ " == 1"]]
                        else return []

                makePair from v1 v2 = do
                    state <- State.get
                    loc <- newLoc $ "parFin_" `Text.append` locNameFromVal (staticMap state) v1 `Text.append` "_" `Text.append` locNameFromVal (staticMap state) v2
                    let label = Label GuardKind $ var1 `Text.append` " == " `Text.append` Text.pack (show (intValMap1 ! v1)) `Text.append` " and " `Text.append`
                                                  var2 `Text.append` " == " `Text.append` Text.pack (show (intValMap2 ! v2))
                    let trans = Transition from (locId loc) [label]
                    return ((TermVal "Pair" [v1, v2], loc), trans)
                                                  
-- no valid pattern match, and so the expression must be semantically invalid; We fail
translateExp _ _ _ _ _ = mzero


-- Transforms the specified location,
-- such that it has an invariant corresponding to the specified label.
-- In case the location already has an invariant, we 'and' the existing and new invariants.
addInvariant :: Label -> Location -> Location
addInvariant invar loc =
    let (label, labels) = Prelude.foldr extendInvar (invar, []) $ locLabels loc
    in  loc{ locLabels = label : labels }
    where
        extendInvar (Label InvariantKind t') (Label _ t, labels) = (Label InvariantKind $ t' `Text.append` " and " `Text.append` t, labels)
        extendInvar label' (label, labels)                       = (label, label' : labels) 


-- Transforms the specified transition,
-- such that is has a guard corresponding to the specified label.
-- In case the transition already has a guard, we 'and' the existing and new guards.
addGuard :: Label -> Transition -> Transition
addGuard guard (Transition from to existing) =
    let (label, labels) = Prelude.foldr extendGuard (guard, []) existing
    in  Transition from to $ label : labels
    where
        extendGuard (Label GuardKind t') (Label _ t, labels) = (Label GuardKind $ t' `Text.append` " and " `Text.append` t, labels)
        extendGuard label' (label, labels)                   = (label, label' : labels)


-- Returns a name representing the specified value,
-- given the specified map from values to their UPPAAL representations.
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


-- Returns a fresh location with a name based on the specified Text
newLoc :: Text -> TransT Location
newLoc t = do
    locID <- nextLocID
    return $ Location locID [] (Just (t `Text.append` locID)) NormalType


-- Returns the UPPAAL representation of the specified value.
-- If the value is a channel end, for which the channel has not yet been declared,
-- we update the staticMap.
-- Note that this could have been done statically, 
-- but this is more convenient if we wish to add dynamic channels in the future.
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
            let newBindings    = Map.fromList [(SendVal id, Text.pack ("ch" ++ show id)), (ReceiveVal id, Text.pack ("ch" ++ show id))]
            let newStaticMap   = staticMap state `Map.union` newBindings
            let newVars        = 
                    case minMaxD state of 
                        Nothing -> Map.empty
                        Just _  -> Map.fromList [(SendVal id, Text.pack ("readySend" ++ show id)), (ReceiveVal id, Text.pack ("readyReceive" ++ show id))]
            let newChannelVars = channelVars state `Map.union` newVars
            State.put state{ staticMap = newStaticMap, channelVars = newChannelVars }
            return $ Text.pack ("ch" ++ show id)


-- Translates a synchronization from our language to its UPPAAL equivalent,
-- represented by a label.
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


-- Returns the next unique integer ID, 
-- and increments the uniqueID counter in the translation state.
nextUniqueID :: TransT Integer
nextUniqueID = State.get >>= 
    (\state -> State.put state{ uniqueID = uniqueID state + 1 } >> 
    return (uniqueID state))


-- Returns the next unique template name,
-- and increments the uniqueID counter for templates in the translation state.
nextTempName :: TransT Text
nextTempName = do
    state <- State.get
    State.put state{ tempID = tempID state + 1 }
    return $ Text.pack ("Temp" ++ show (tempID state))


-- Returns the next unique location ID,
-- and increments the uniqueID counter for locations in the translation state.
nextLocID :: TransT Text
nextLocID = do
    state <- State.get
    State.put state{ locID = locID state + 1 }
    return $ Text.pack (show (locID state))