module Ast
    ( Exp(..)
    ) where

import Data.Map as Map

type Name = String

type Subst = Map Name Val

data Exp = RefExp Name
         | ConExp Con
         | TermConsExp Name
         | AppExp Exp Exp
         | FixExp Exp
         | MatchExp MatchBody                -- We ensure at least one branch by use of 'MatchBody'
         | InvarExp Ctt [Name] Subst Exp Exp
         | LetExp Name Exp Exp
         | SyncExp SyncBody                  -- We ensure at least one branch by use of 'SyncBody'
         | GuardExp Exp Ctt
         | ParExp Exp Exp
         
data MatchBody = SingleMatch Pat Exp | MultiMatch Pat Exp MatchBody

data SyncBody = SingleSync Sync Exp | MultiSync Sync Exp SyncBody

data Pat = RefPat Name | TermPat Name [Pat]

data Sync = ReceiveSync Name Name | SendSync Name Name (Maybe Val)

data Ctt = LandCtt Ctt Ctt 
         | ClockLeqCtt (Either Name Val) Integer -- We account for substitution in clock constraints by use of 'Either'
         | ClockGeqCtt (Either Name Val) Integer --
         | ClockLCtt   (Either Name Val) Integer --
         | ClockGCtt   (Either Name Val) Integer --

data Con = ResetCon | OpenCon | GetCon | SetCon

data Val = ConVal
         | TermVal [Val]
         | MatchVal MatchBody
         | ClkVal Integer     -- Integer corresponds to clock ID
         | ReceiveVal Integer -- Integer corresponds to channel ID
         | SendVal Integer    --
         | PinVal Integer     -- Integer corresponds to pin ID
         | WorldVal