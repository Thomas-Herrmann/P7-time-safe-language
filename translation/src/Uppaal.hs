{-# LANGUAGE OverloadedStrings #-}

module Uppaal
    ( Query
    , Declaration
    , System(..)
    , Template(..)
    , Location(..)
    , Label(..)
    , Kind(..)
    , Transition(..)
    , systemToXML
    ) where

import Text.XML
import Data.Map as Map
import Data.Text as Text

type Query = Text
type Declaration = Text

data System = System { sysDecls :: [Declaration]
                     , sysTemplates :: [Template]
                     , sysSystemDecls :: [Declaration]
                     , sysQueries :: [Query]
                     }

data Template = Template { temName :: Text
                         , temLocations :: [Location]
                         , temTransitions :: [Transition] 
                         , temDecls :: [Declaration]
                         , temInit :: Text
                         , temFinal :: Text
                         }

data Location = Location { locId :: Text
                         , locLabels :: [Label]
                         , locName :: Maybe Text
                         }

data Label = Label Kind Text

data Kind = InvariantKind | GuardKind | AssignmentKind | SyncKind

data Transition = Transition { traSource :: Text
                             , traTarget :: Text
                             , traLabels :: [Label]
                             }


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
         [textNode "system" (Text.concat $ sysSystemDecls sys)]) -- TODO queries

instance Renderable Template where
    toXML tem = NodeElement $ Element "template" Map.empty 
        ([textNode "name" (temName tem)] ++
         [textNode "declaration" (Text.concat $ temDecls tem)] ++
         Prelude.map toXML (temLocations tem) ++
         [NodeElement $ Element "init" (Map.singleton "ref" (temInit tem)) []] ++ --todo check
         Prelude.map toXML (temTransitions tem)
        )

instance Renderable Location where
    toXML loc = NodeElement $ Element "location" (Map.singleton "id" (locId loc)) 
        (Prelude.map toXML (locLabels loc) ++
         case locName loc of
             Just name -> [textNode "name" name]
             Nothing -> []
        )
        
instance Renderable Label where
    toXML (Label kind content) = textNodeAttr "label" (Map.singleton "kind" (kindText kind)) content 

instance Renderable Transition where
    toXML tra = NodeElement $ Element "transition" Map.empty 
        ([ NodeElement $ Element "source" (Map.singleton "ref" (traSource tra)) []
         , NodeElement $ Element "target" (Map.singleton "ref" (traTarget tra)) []
         ] ++ Prelude.map toXML (traLabels tra))


systemToXML :: System -> Document
systemToXML sys = case toXML sys of
    NodeElement el -> Document (Prologue [] Nothing []) el []