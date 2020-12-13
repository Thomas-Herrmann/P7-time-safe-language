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
    , negateCtt
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
         deriving (Eq, Ord, Show, Read)
         
data MatchBody = SingleMatch Pat Exp | MultiMatch Pat Exp MatchBody deriving (Eq, Ord, Show, Read)

data SyncBody = SingleSync Sync Exp | MultiSync Sync Exp SyncBody deriving (Eq, Ord, Show, Read)

data Pat = RefPat Name | TermPat Name [Pat] deriving (Eq, Ord, Show, Read)

data Sync = ReceiveSync (Either Name Val) Name 
          | SendSync (Either Name Val) Name (Maybe Val)
          | GetSync (Either Name Val) Bool
          | SetSync (Either Name Val) Bool
          deriving (Eq, Ord, Show, Read)

data Ctt = LandCtt Ctt Ctt 
         | LorCtt Ctt Ctt
         | ClockLeqCtt (Either Name Val) Integer -- We account for substitution in clock constraints by use of 'Either'
         | ClockGeqCtt (Either Name Val) Integer --
         | ClockLCtt   (Either Name Val) Integer --
         | ClockGCtt   (Either Name Val) Integer --
         deriving (Eq, Ord, Show, Read)


negateCtt :: Ctt -> Ctt
negateCtt (LandCtt g1 g2)     = LorCtt (negateCtt g1) (negateCtt g2)
negateCtt (LorCtt g1 g2)      = LandCtt (negateCtt g1) (negateCtt g2)
negateCtt (ClockLeqCtt clk n) = ClockGCtt clk n
negateCtt (ClockGeqCtt clk n) = ClockLCtt clk n
negateCtt (ClockLCtt clk n)   = ClockGeqCtt clk n
negateCtt (ClockGCtt clk n)   = ClockLeqCtt clk n


data Con = ResetCon deriving (Eq, Ord, Show, Read)

data Val = ConVal Con
         | TermVal Name [Val]
         | MatchVal MatchBody -- We ensure at least one branch by use of 'MatchBody'
         | RecMatchVal Name MatchBody
         | ClkVal Integer     -- Integer corresponds to clock ID
         | ReceiveVal Integer -- Integer corresponds to channel ID
         | SendVal Integer    --
         | InPinVal Integer   -- Integer corresponds to in pin ID
         | OutPinVal Integer  -- Integer corresponds to out pin ID
         deriving (Eq, Ord, Show, Read)


-- Type class representing the definitions of free variables and explicit substitutions
class Substitutable a where
    fv :: a -> Set Name
    substitute :: a -> Subst -> a

instance Substitutable Exp where
    fv (RefExp x)                    = Set.singleton x
    fv (AppExp e1 e2)                = fv e1 `Set.union` fv e2
    fv (FixExp e)                    = fv e   
    fv (ValExp (MatchVal body))      = fv body
    fv (ValExp (RecMatchVal x body)) = fv body `Set.difference` Set.singleton x
    fv (InvarExp _ _ _ e1 e2)        = fv e1 `Set.union` fv e2
    fv (LetExp x e1 e2)              = (fv e1 `Set.union` fv e2) `Set.difference` Set.singleton x
    fv (SyncExp body)                = fv body
    fv (GuardExp e _)                = fv e
    fv (ParExp e1 e2)                = fv e1 `Set.union` fv e2
    fv _                             = Set.empty

    substitute (RefExp x) subst | x `Map.member` subst = ValExp $ subst ! x
                                | otherwise            = RefExp x

    substitute (AppExp e1 e2) subst                = AppExp (substitute e1 subst) (substitute e2 subst)
    substitute (FixExp e) subst                    = FixExp $ substitute e subst
    substitute (ValExp (MatchVal body)) subst      = ValExp $ MatchVal (substitute body subst)
    substitute (ValExp (RecMatchVal x body)) subst = ValExp $ RecMatchVal x (substitute body $ Map.delete x subst)
    substitute (InvarExp g xs subst e1 e2) subst'  = InvarExp (substitute g subst') xs subst'' (substitute e1 subst') (substitute e2 filtered)
        where
            pred k _ = k `Prelude.notElem` xs
            filtered = Map.filterWithKey pred subst'
            subst''  = subst `Map.union` Map.map (\v -> TermVal "Just" [v]) filtered

    substitute (LetExp x e1 e2) subst = LetExp x (substitute e1 subst) (substitute e2 $ Map.delete x subst)
    substitute (SyncExp body) subst   = SyncExp $ substitute body subst
    substitute (GuardExp e g) subst   = GuardExp (substitute e subst) (substitute g subst)
    substitute (ParExp e1 e2) subst   = ParExp (substitute e1 subst) (substitute e2 subst)

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
    fv _                        = Set.empty

    substitute (ReceiveSync (Left x) y) subst      | x `Map.member` subst = ReceiveSync (Right (subst ! x)) y
    substitute (SendSync (Left x) y Nothing) subst | x `Map.member` subst && y `Map.member` subst = SendSync (Right (subst ! x)) y (Just (subst ! y))
    substitute (SendSync (Left x) y val) subst     | x `Map.member` subst = SendSync (Right (subst ! x)) y val
    substitute (SendSync x y Nothing) subst        | y `Map.member` subst = SendSync x y (Just (subst ! y))
    substitute (GetSync (Left x) b) subst          | x `Map.member` subst = GetSync (Right (subst ! x)) b
    substitute (SetSync (Left x) b) subst          | x `Map.member` subst = SetSync (Right (subst ! x)) b                                                   

    substitute q _ = q

instance Substitutable Ctt where
    fv (LandCtt g1 g2)          = fv g1 `Set.union` fv g2
    fv (LorCtt g1 g2)           = fv g1 `Set.union` fv g2
    fv (ClockLeqCtt (Left x) _) = Set.singleton x
    fv (ClockGeqCtt (Left x) _) = Set.singleton x
    fv (ClockLCtt (Left x) _)   = Set.singleton x
    fv (ClockGCtt (Left x) _)   = Set.singleton x
    fv _                        = Set.empty

    substitute (LandCtt g1 g2) subst                                 = LandCtt (substitute g1 subst) (substitute g2 subst)
    substitute (LorCtt g1 g2) subst                                  = LorCtt (substitute g1 subst) (substitute g2 subst)
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
    iv _                 = Set.empty

