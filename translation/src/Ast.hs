module Ast
    ( Exp(..)
    , Pat(..)
    , Val(..)
    , MatchBody(..)
    , SyncBody(..)
    , Sync(..)
    , Con(..)
    , Ctt(..)
    , Name
    , Subst
    , Substitutable(..)
    , Introducable(..)
    ) where

import Data.Map as Map
import Data.Set as Set

type Name = String

type Subst = Map Name Val

data Exp = RefExp Name
         | AppExp Exp Exp
         | FixExp Exp
         | InvarExp Ctt [Name] Subst Exp Exp
         | LetExp Name Exp Exp
         | SyncExp SyncBody                  -- We ensure at least one branch by use of 'SyncBody'
         | GuardExp Exp Ctt
         | ParExp Exp Exp
         | ValExp Val
         deriving (Eq, Ord, Show)
         
data MatchBody = SingleMatch Pat Exp | MultiMatch Pat Exp MatchBody deriving (Eq, Ord, Show)

data SyncBody = SingleSync Sync Exp | MultiSync Sync Exp SyncBody deriving (Eq, Ord, Show)

data Pat = RefPat Name | TermPat Name [Pat] deriving (Eq, Ord, Show)

data Sync = ReceiveSync (Either Name Val) Name 
          | SendSync (Either Name Val) Name (Maybe Val)
          | GetSync (Either Name Val) Bool
          | SetSync (Either Name Val) Bool
          deriving (Eq, Ord, Show)

data Ctt = LandCtt Ctt Ctt 
         | ClockLeqCtt (Either Name Val) Integer -- We account for substitution in clock constraints by use of 'Either'
         | ClockGeqCtt (Either Name Val) Integer --
         | ClockLCtt   (Either Name Val) Integer --
         | ClockGCtt   (Either Name Val) Integer --
         deriving (Eq, Ord, Show)

data Con = ResetCon | OpenCon deriving (Eq, Ord, Show)

data Val = ConVal Con
         | TermVal Name [Val]
         | MatchVal MatchBody -- We ensure at least one branch by use of 'MatchBody'
         | ClkVal Integer     -- Integer corresponds to clock ID
         | ReceiveVal Integer -- Integer corresponds to channel ID
         | SendVal Integer    --
         | PinVal Integer     -- Integer corresponds to pin ID
         | WorldVal
         deriving (Eq, Ord, Show)


class Substitutable a where
    fv :: a -> Set Name
    substitute :: a -> Subst -> a

instance Substitutable Exp where
    fv (RefExp x)               = Set.singleton x
    fv (AppExp e1 e2)           = fv e1 `Set.union` fv e2
    fv (FixExp e)               = fv e   
    fv (ValExp (MatchVal body)) = fv body
    fv (InvarExp _ _ _ e1 e2)   = fv e1 `Set.union` fv e2
    fv (LetExp x e1 e2)         = (fv e1 `Set.union` fv e2) `Set.difference` Set.singleton x
    fv (SyncExp body)           = fv body
    fv (GuardExp e _)           = fv e
    fv (ParExp e1 e2)           = fv e1 `Set.union` fv e2
    fv _                        = Set.empty

    substitute (RefExp x) subst | x `Map.member` subst = ValExp $ subst ! x
                                | otherwise            = RefExp x

    substitute (AppExp e1 e2) subst               = AppExp (substitute e1 subst) (substitute e2 subst)
    substitute (FixExp e) subst                   = FixExp $ substitute e subst
    substitute (ValExp (MatchVal body)) subst     = ValExp $ MatchVal (substitute body subst)
    substitute (InvarExp g xs subst e1 e2) subst' = InvarExp (substitute g subst') xs subst'' (substitute e1 subst') (substitute e2 filtered)
        where
            pred k _ = not (k `Prelude.elem` xs)
            filtered = Map.filterWithKey pred subst'
            subst''  = subst `Map.union` (Map.map (\v -> TermVal "Just" [v]) filtered)

    substitute (LetExp x e1 e2) subst | x `Map.member` subst = LetExp x (substitute e1 subst) e2
                                      | otherwise            = LetExp x (substitute e1 subst) (substitute e2 subst)

    substitute (SyncExp body) subst = SyncExp $ substitute body subst
    substitute (GuardExp e g) subst = GuardExp (substitute e subst) (substitute g subst)
    substitute (ParExp e1 e2) subst = ParExp (substitute e1 subst) (substitute e2 subst)

    substitute e _ = e

instance Substitutable MatchBody where
    fv (SingleMatch p e)    = fv e `Set.difference` iv p
    fv (MultiMatch p e rem) = (fv e `Set.difference` iv p) `Set.union` fv rem

    substitute (SingleMatch p e) subst = SingleMatch p $ substitute e filtered
        where
            pred k _ = not (k `Set.member` iv p)
            filtered = Map.filterWithKey pred subst

    substitute (MultiMatch p e rem) subst = MultiMatch p (substitute e filtered) $ substitute rem subst
        where
            pred k _ = not (k `Set.member` iv p)
            filtered = Map.filterWithKey pred subst 

instance Substitutable SyncBody where
    fv (SingleSync q e)    = (fv q `Set.union` fv e) `Set.difference` iv q
    fv (MultiSync q e rem) = ((fv q `Set.union` fv e) `Set.difference` iv q) `Set.union` fv rem

    substitute (SingleSync q e) subst = SingleSync (substitute q subst) $ substitute e filtered
        where
            pred k _ = not (k `Set.member` iv q)
            filtered = Map.filterWithKey pred subst

    substitute (MultiSync q e rem) subst = MultiSync (substitute q subst) (substitute e filtered) $ substitute rem subst
        where
            pred k _ = not (k `Set.member` iv q)
            filtered = Map.filterWithKey pred subst 

instance Substitutable Sync where
    fv (ReceiveSync (Left x) _) = Set.singleton x
    fv (SendSync (Left x) y _)  = Set.fromList [x, y]
    fv (SendSync (Right _) y _) = Set.singleton y
    fv (GetSync (Left x) _)     = Set.singleton x
    fv (SetSync (Left x) _)     = Set.singleton x
    fv q                        = Set.empty

    substitute (ReceiveSync (Left x) y) subst      | x `Map.member` subst = ReceiveSync (Right (subst ! x)) y
    substitute (SendSync (Left x) y Nothing) subst | x `Map.member` subst && y `Map.member` subst = SendSync (Right (subst ! x)) y (Just (subst ! y))
    substitute (SendSync (Left x) y val) subst     | x `Map.member` subst = SendSync (Right (subst ! x)) y val
    substitute (SendSync x y Nothing) subst        | y `Map.member` subst = SendSync x y (Just (subst ! y))
    substitute (GetSync (Left x) b) subst          | x `Map.member` subst = GetSync (Right (subst ! x)) b
    substitute (SetSync (Left x) b) subst          | x `Map.member` subst = SetSync (Right (subst ! x)) b                                                   

    substitute q _ = q

instance Substitutable Ctt where
    fv (LandCtt g1 g2)          = fv g1 `Set.union` fv g2
    fv (ClockLeqCtt (Left x) _) = Set.singleton x
    fv (ClockGeqCtt (Left x) _) = Set.singleton x
    fv (ClockLCtt (Left x) _)   = Set.singleton x
    fv (ClockGCtt (Left x) _)   = Set.singleton x
    fv _                        = Set.empty

    substitute (LandCtt g1 g2) subst                                 = LandCtt (substitute g1 subst) (substitute g2 subst)
    substitute (ClockLeqCtt (Left x) n) subst | x `Map.member` subst = ClockLeqCtt (Right (subst ! x)) n
    substitute (ClockGeqCtt (Left x) n) subst | x `Map.member` subst = ClockGeqCtt (Right (subst ! x)) n
    substitute (ClockLCtt (Left x) n) subst   | x `Map.member` subst = ClockLCtt (Right (subst ! x)) n
    substitute (ClockGCtt (Left x) n) subst   | x `Map.member` subst = ClockGCtt (Right (subst ! x)) n
    substitute e _ = e

class Introducable a where
    iv :: a -> Set Name

instance Introducable Pat where
    iv (RefPat x)     = Set.singleton x
    iv (TermPat _ ps) = Prelude.foldr (Set.union . iv) Set.empty ps

instance Introducable Sync where
    iv (ReceiveSync _ y) = Set.singleton y
    iv q                 = Set.empty

