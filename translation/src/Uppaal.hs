{-# LANGUAGE OverloadedStrings #-}

module Uppaal
    ( Declaration
    , System(..)
    , Template(..)
    , Location(..)
    , Label(..)
    , Kind(..)
    , Transition(..)
    , Query(..)
    , systemToXML
    , pruneTemplate
    , pruneSystem
    ) where

import Text.XML
import Data.Map as Map
import Data.Text as Text
import Data.List as List

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

data Location = Location { 
                           locId :: Text
                         , locLabels :: [Label]
                         , locName :: Maybe Text
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
                nameList ++ Prelude.map toXML (locLabels loc)
        where
            nameList =
                case locName loc of
                    Just name -> [textNode "name" name]
                    Nothing -> []
        
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

pruneSystem :: System -> System
pruneSystem sys = sys { sysTemplates = Prelude.map pruneTemplate (sysTemplates sys)}

pruneTemplate :: Template -> Template
pruneTemplate temp = let (newLocs, newTrans) = prune (temLocations temp, temTransitions temp) (temLocations temp)
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
               _ | lId /= initLoc && -- Don't remove inital locations
                   Prelude.length incomingTransL == 1 && Prelude.length outgoingTransL == 1 && -- Only remove locations with 1 incoming and 1 outgoing transition
                   Prelude.null (locLabels l) && Prelude.null (traLabels iTran) && Prelude.null (traLabels oTran) ->
                    prunePass (List.delete l locs, newTran:List.delete iTran (List.delete oTran trans)) ls
                 | Prelude.null incomingTransL && Prelude.null outgoingTransL ->
                    prunePass (List.delete l locs, trans) ls
                 | otherwise -> 
                    prunePass (locs, trans) ls
            where
                lId = locId l

                incomingTransL = Prelude.filter (\tra -> lId == traTarget tra) trans
                outgoingTransL = Prelude.filter (\tra -> lId == traSource tra) trans

                iTran = List.head incomingTransL
                oTran = List.head outgoingTransL
                newTran = Transition {traSource = traSource iTran, traTarget = traTarget oTran, traLabels = []}