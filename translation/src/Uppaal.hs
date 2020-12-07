{-# LANGUAGE OverloadedStrings #-}

module Uppaal
    ( Declaration
    , System(..)
    , Template(..)
    , Location(..)
    , LocationType(..)
    , Label(..)
    , Kind(..)
    , Transition(..)
    , Query(..)
    , systemToXML
    , pruneTemplate
    ) where

import Text.XML
import Data.Map as Map
import Data.Text as Text
import Data.List as List
import Data.Maybe

type Declaration = Text

data System = System { 
                       sysDecls :: [Declaration]
                     , sysTemplates :: [Template]
                     , sysSystemDecls :: [Declaration]
                     , sysQueries :: [Query]
                     } 
                     deriving (Eq, Ord)

data Template = Template { 
                           temName :: Text
                         , temLocations :: [Location]
                         , temTransitions :: [Transition] 
                         , temDecls :: [Declaration]
                         , temInit :: Text
                         , temFinal :: Text
                         }
                         deriving (Eq, Ord)

data LocationType = NormalType | UrgentType | CommittedType deriving (Eq, Ord, Show)

data Location = Location { 
                           locId :: Text
                         , locLabels :: [Label]
                         , locName :: Maybe Text
                         , locType :: LocationType
                         }
                         deriving (Eq, Ord, Show)

data Label = Label Kind Text deriving (Eq, Ord, Show)

data Kind = InvariantKind | GuardKind | AssignmentKind | SyncKind deriving (Eq, Ord, Show)

data Transition = Transition { 
                               traSource :: Text
                             , traTarget :: Text
                             , traLabels :: [Label]
                             }
                             deriving (Eq, Ord, Show)

data Query = Query Text Text deriving (Eq, Ord)


kindText :: Kind -> Text
kindText InvariantKind = "invariant"
kindText GuardKind = "guard"
kindText AssignmentKind = "assignment"
kindText SyncKind = "synchronisation"

textNodeAttr :: Text -> Map Name Text -> Text -> Node
textNodeAttr name attr content = NodeElement $ Element (Name name Nothing Nothing) attr [NodeContent content]


textNode :: Text -> Text -> Node
textNode name content = textNodeAttr name Map.empty content


class Renderable a where
    toXML :: a -> Node

instance Renderable System where
    toXML sys = NodeElement $ Element "nta" Map.empty 
        ([textNode "declaration" (Text.concat $ sysDecls sys)] ++ 
         Prelude.map toXML (sysTemplates sys) ++
         [textNode "system" (Text.concat $ sysSystemDecls sys)] ++
         [NodeElement $ Element "queries" Map.empty (Prelude.map toXML (sysQueries sys))]
        ) 

instance Renderable Template where
    toXML tem = NodeElement $ Element "template" Map.empty 
        ([textNode "name" (temName tem)] ++
         [textNode "declaration" (Text.concat $ temDecls tem)] ++
         Prelude.map toXML (temLocations tem) ++
         [NodeElement $ Element "init" (Map.singleton "ref" (temInit tem)) []] ++
         Prelude.map toXML (temTransitions tem)
        )

instance Renderable Location where
    toXML loc = NodeElement $ Element "location" (Map.singleton "id" (locId loc)) $ 
                nameList ++ Prelude.map toXML (locLabels loc) ++ typ
        where
            nameList =
                case locName loc of
                    Just name -> [textNode "name" name]
                    Nothing -> []
            typ = 
                case locType loc of
                    NormalType -> []
                    UrgentType -> [NodeElement $ Element "urgent" Map.empty []]
                    CommittedType -> [NodeElement $ Element "committed" Map.empty []]
        
instance Renderable Label where
    toXML (Label kind content) = textNodeAttr "label" (Map.singleton "kind" (kindText kind)) content 

instance Renderable Transition where
    toXML tra = NodeElement $ Element "transition" Map.empty 
        ([ NodeElement $ Element "source" (Map.singleton "ref" (traSource tra)) []
         , NodeElement $ Element "target" (Map.singleton "ref" (traTarget tra)) []
         ] ++ Prelude.map toXML (traLabels tra))

instance Renderable Query where
    toXML (Query formula comment) = NodeElement $ Element "query" Map.empty 
        [textNode "formula" formula, textNode "comment" comment]

systemToXML :: System -> Document
systemToXML sys = case toXML sys of
    NodeElement el -> Document (Prologue [] Nothing []) el []

-- Continously goes over every location in the template, trying to remove locations each pass.
-- Once no more locations are removed in a pass, no more passes are done.  
pruneTemplate :: Text -> Template -> Template
pruneTemplate clkD temp = let (newLocs, newTrans) = prune (temLocations temp, temTransitions temp) (temLocations temp)
                           in temp { temLocations = newLocs, temTransitions = newTrans}
    where
        initLoc = temInit temp

        prune (locs, trans) ls = 
            let (newLocs, newTrans) = prunePass (locs, trans) ls in 
                if Prelude.length newLocs == Prelude.length locs 
                    then (locs, trans) 
                    else prune (newLocs, newTrans) ls

        prunePass :: ([Location], [Transition]) -> [Location] -> ([Location], [Transition])
        prunePass (locs, trans) [] = (locs, trans)
        prunePass (locs, trans) (l:ls) =
            case () of
                   -- Prune unconnected locations 
               _ | Prelude.null incomingTransL && Prelude.null outgoingTransL ->
                    prunePass (List.delete l locs, trans) ls
                   -- Prune simple locations with a single outgoing and a single incoming transition. Create a new transition connected the two now unconnected locations
                 | lId /= initLoc && -- Don't remove inital locations
                   Prelude.length incomingTransL == 1 && Prelude.length outgoingTransL == 1 && -- Only remove locations with 1 incoming and 1 outgoing transition
                   Prelude.null (locLabels l) && Prelude.null (traLabels iTran) && Prelude.null (traLabels oTran) ->
                    let newTran = Transition {traSource = traSource iTran, traTarget = traTarget oTran, traLabels = []}
                    in prunePass (List.delete l locs, newTran:List.delete iTran (List.delete oTran trans)) ls
                   -- Prune locations with a single outgoing and a single outgoing transition, taking into account updates to clkD
                 | Prelude.length incomingTransL == 1 && Prelude.length outgoingTransL == 1 && -- Only remove locations with 1 incoming and 1 outgoing transition
                   Prelude.length (locLabels l) == 1 && Prelude.length (traLabels iTran) == 2 && Prelude.length (traLabels oTran) == 2 &&
                   isJust (traGetClkDGuard iTran) && isJust (traGetClkDUpdate iTran) && -- Ensure only transitions with the correct labels are pruned
                   isJust (traGetClkDGuard oTran) && isJust (traGetClkDUpdate oTran) &&
                   locType l == NormalType && isJust (locGetClkDInvariant l) && isJust (fst (findLocsFromTran iTran)) -> 
                    let (Just l2, _) = findLocsFromTran iTran
                        invariantTime1 = labelExractTime $ fromJust $ locGetClkDInvariant l -- Find Y in invariant of form "clkDX < Y" of first location
                        invariantTime2 = labelExractTime $ fromJust $ locGetClkDInvariant l2 -- Find Y in invariant of form "clkDX < Y" of second location
                        transitionTime1 = labelExractTime $ fromJust $ traGetClkDGuard oTran -- Find Y in guard of form "clkX >= Y" of first transition
                        transitionTime2 = labelExractTime $ fromJust $ traGetClkDGuard iTran -- Find Y in guard of form "clkX >= Y" of second transition
                        newInvariant = Label InvariantKind $ clkDInvariantPrefix `Text.append` Text.pack (show $ invariantTime1 + invariantTime2) -- Construct new invariant
                        newGuard = Label GuardKind $ clkDGuardPrefix `Text.append` Text.pack (show $ transitionTime1 + transitionTime2) -- Construct new guard
                        newUpdate = Label AssignmentKind clkDUpdateText -- Construct update label
                        newLoc = Location {locId = locId l2, locLabels = [newInvariant], locName = locName l2, locType = locType l2} -- Construct updated version of first location
                        newTran = Transition {traSource = locId newLoc, traTarget = traTarget oTran, traLabels = [newGuard, newUpdate]} -- Construct new transition
                    in prunePass (newLoc:List.delete l2 (List.delete l locs), newTran:List.delete iTran (List.delete oTran trans)) (List.delete l2 ls)
                 | otherwise -> 
                    prunePass (locs, trans) ls
            where
                lId = locId l

                incomingTransL = Prelude.filter (\tra -> lId == traTarget tra) trans
                outgoingTransL = Prelude.filter (\tra -> lId == traSource tra) trans

                iTran = List.head incomingTransL
                oTran = List.head outgoingTransL

                -- Tries to find the corresponding locations to an edge
                findLocsFromTran tran = (List.find (\loc -> locId loc == traSource tran) locs, 
                                         List.find (\loc -> locId loc == traTarget tran) locs)
        
        clkDGuardPrefix = clkD `Text.append` " >= "
        clkDUpdateText = clkD `Text.append` " := 0"
        clkDInvariantPrefix = clkD `Text.append` " < "
        
        traGetClkDGuard t = List.find (\(Label kind content) -> kind == GuardKind && Text.isPrefixOf clkDGuardPrefix content) (traLabels t)
        traGetClkDUpdate t = List.find (\(Label kind content) -> kind == AssignmentKind && clkDUpdateText == content) (traLabels t)
        locGetClkDInvariant l = List.find (\(Label kind content) -> kind == InvariantKind && Text.isPrefixOf clkDInvariantPrefix content) (locLabels l)

        -- Extracts the time of a label based on its type and prefix
        labelExractTime :: Label -> Int
        labelExractTime (Label kind content) = 
            let maybeText = case kind of
                                GuardKind -> Text.stripPrefix clkDGuardPrefix content
                                InvariantKind -> Text.stripPrefix clkDInvariantPrefix content
            in read (Text.unpack (fromJust maybeText))