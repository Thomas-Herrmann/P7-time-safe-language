module Example
    ( mainFun
    , clockNames
    , inPinNames
    , outPinNames
    , channelNames
    ) where

import Ast
import qualified Data.Map as Map


constructTuple :: Name -> [Exp] -> Exp
constructTuple name [] = ValExp $ TermVal name []
constructTuple name (x:xs) = constructTuple' (AppExp (ValExp $ TermVal name []) x) xs
    where
        constructTuple' :: Exp -> [Exp] -> Exp
        constructTuple' c [] = c
        constructTuple' c (x:xs) = constructTuple' (AppExp c x) xs

patLetExp :: Pat -> Exp -> Exp -> Exp
patLetExp pat e1 e2 = AppExp (ValExp $ MatchVal $ SingleMatch pat e2) e1

presetup e = LetExp "tt" (ValExp $ TermVal "true" []) $
             LetExp "ff" (ValExp $ TermVal "false" []) e 

clockNames = ["clkX1", "clkY1", "clkX2", "clkY2"]
inPinNames = ["pSen1", "pSen2"]
outPinNames = ["pLig1", "pLig2"]
channelNames = [("wgSen1", "wgRec1"), ("wgSen2", "wgRec2"), ("rSen1", "rRec1"), ("rSen2", "rRec2")]

statePat = TermPat "State" (map RefPat ["clkX", "clkY", "pSen", "pLig", "wgSen", "wgRec", "rSen", "rRec"])
makeState args = constructTuple "State" (map RefExp args)

mainFun = presetup $ LetExp "conFun" conFun $ ParExp 
    (AppExp (RefExp "conFun") (constructTuple "cfArgs" (map RefExp ["clkX1", "clkY1", "pSen1", "pLig1", "wgSen1", "wgRec2", "rSen1", "rRec2"])))
    (AppExp (RefExp "conFun") (constructTuple "cfArgs" (map RefExp ["clkX2", "clkY2", "pSen2", "pLig2", "wgSen2", "wgRec1", "rSen2", "rRec1"])))

conFun = FixExp $ ValExp $ MatchVal $ SingleMatch (RefPat "R1") $
    ValExp $ MatchVal $ SingleMatch statePat $
        SyncExp $ 
            MultiSync (GetSync (Left "pSen") True) (AppExp o2 state) $
            SingleSync (SendSync (Left "tt") "rSen" Nothing) (AppExp (RefExp "R1") state)
    where state = makeState ["clkX", "clkY", "pSen", "pLig", "wgSen", "wgRec", "rSen", "rRec"]

o2 = FixExp $ ValExp $ MatchVal $ SingleMatch (RefPat "R2") $
    ValExp $ MatchVal $ SingleMatch statePat $
        SyncExp $ 
            MultiSync (SendSync (Left "tt") "wgSen" Nothing) (AppExp (RefExp "R2") state) $
            MultiSync (ReceiveSync (Left "x") "rRec") o3 $
            SingleSync (SendSync (Left "tt") "rSen" Nothing) $
                SyncExp $ 
                    MultiSync (ReceiveSync (Left "x") "rRec") o3 $
                    SingleSync (SendSync (Left "tt") "wgSen" Nothing) $
                        SyncExp $ SingleSync (ReceiveSync (Left "y") "rRec") o3
    where state = makeState ["clkX", "clkY", "pSen", "pLig", "wgSen", "wgRec", "rSen", "rRec"]

o3 = patLetExp (TermPat "pair" [RefPat "pLig'", RefPat "clkX'"]) (constructTuple "pair" [SyncExp $ SingleSync (SetSync (Left "pLig") True) (RefExp "pLig"), AppExp (ValExp $ ConVal ResetCon) (RefExp "clkX")]) $
    LetExp "pLig''" (GuardExp (SyncExp $ SingleSync (SetSync (Left "pLig'") True) (RefExp "pLig'")) (ClockGCtt (Left "clkX'") 2)) (AppExp o4 state)
    where state = makeState ["clkX'", "clkY", "pSen", "pLig'", "wgSen", "wgRec", "rSen", "rRec"]

o4 = FixExp $ ValExp $ MatchVal $ SingleMatch (RefPat "G1") $
    ValExp $ MatchVal $ SingleMatch statePat $
        LetExp "clkX'" (ValExp $ ConVal ResetCon) $
            patLetExp (TermPat "triple" [RefPat "x", RefPat "pSen'", RefPat "wgRec'"]) 
                (InvarExp (ClockLCtt (Left "clkX'") 15) [] Map.empty 
                    (SyncExp $ MultiSync (GetSync (Left "pSen") True) (constructTuple "triple" [ValExp $ TermVal "zero" [], RefExp "pSen", RefExp "wgRec"]) $
                     SingleSync (ReceiveSync (Left "wgRec") "y") (constructTuple "triple" [ValExp $ TermVal "one" [], RefExp "pSen", RefExp "wgRec"])) 
                    (constructTuple "triple" [ValExp $ TermVal "two" [], RefExp "pSen", RefExp "wgRec"]))
                (ValExp $ MatchVal $ 
                    MultiMatch (RefPat "zero") (AppExp (RefExp "G1") state) $
                    MultiMatch (RefPat "one") (AppExp o5 state) $
                    SingleMatch (RefPat "two") o6)
    where state = makeState ["clkX'", "clkY", "pSen'", "pLig", "wgSen", "wgRec'", "rSen", "rRec"]

o5 = LetExp "clkY'" (AppExp (ValExp $ ConVal ResetCon) (RefExp "clkY")) $
    FixExp $ ValExp $ MatchVal $ SingleMatch (RefPat "G2") $
        ValExp $ MatchVal $ SingleMatch statePat $
            patLetExp (TermPat "triple" [RefPat "y", RefPat "pSen'", RefPat "clkX''"])
                (LetExp "clkX'" (AppExp (ValExp $ ConVal ResetCon) (RefExp "clkX")) $
                    InvarExp (ClockLCtt (Left "clkX'") 15) [] Map.empty 
                        (SyncExp $ SingleSync (GetSync (Left "pSen'") True) (constructTuple "triple" [ValExp $ TermVal "one" [], RefExp "pSen'", RefExp "clkX'"])) 
                        (constructTuple "triple" [ValExp $ TermVal "two" [], RefExp "pSen'", RefExp "clkX'"]))
                (AppExp (ValExp $ MatchVal $ 
                    MultiMatch (TermPat "one" []) (AppExp (RefExp "G2") state) $
                    SingleMatch (TermPat "two" []) o6) (RefExp "y"))
    where state = makeState ["clkX''", "clkY", "pSen'", "pLig", "wgSen", "wgRec", "rSen", "rRec"]

o6 = patLetExp (TermPat "pair" [RefPat "pLig''", RefPat "clkX'''"]) (constructTuple "pair" [SyncExp $ SingleSync (SetSync (Left "pLig'") True) (RefExp "pLig'"), AppExp (ValExp $ ConVal ResetCon) (RefExp "clikX''")]) $
    GuardExp (SyncExp $ SingleSync (SetSync (Left "pLig''") False) (AppExp (RefExp "R1") state)) (ClockGeqCtt (Left "clkX'''") 3)
    where state = makeState ["clkX'''", "clkY", "pSen'", "pLig''", "wgSen", "wgRec", "rSen", "rRec"]
