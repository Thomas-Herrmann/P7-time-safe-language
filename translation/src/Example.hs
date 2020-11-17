module Example 
    ( mainFun
    , clockNames
    , inPinNames
    , outPinNames
    , worldName
    , testFun
    ) where

import Ast
import qualified Data.Map as Map

tcTrue = TermVal "true" []
tcFalse = TermVal "false" []
tcR1 = TermVal "R1" []
tcR2 = TermVal "R2" []
tcG1 = TermVal "R3" []
tcG2 = TermVal "R4" []

tcTruePat = TermPat "true" []
tcFalsePat = TermPat "true" []

constructTuple :: Name -> [Exp] -> Exp
constructTuple name [] = RefExp name
constructTuple name (x:xs) = constructTuple' (AppExp (RefExp name) x) xs
    where
        constructTuple' :: Exp -> [Exp] -> Exp
        constructTuple' c [] = c
        constructTuple' c (x:xs) = constructTuple' (AppExp c x) xs

patLetExp :: Pat -> Exp -> Exp -> Exp
patLetExp pat e1 e2 = AppExp (ValExp $ MatchVal $ SingleMatch pat e2) e1

callLoop :: [Exp] -> Exp
callLoop args = AppExp (RefExp "loop") (constructTuple "cfArgs" args)

presetup e = LetExp "tt" (ValExp $ TermVal "true" []) $
             LetExp "ff" (ValExp $ TermVal "false" []) e 

clockNames = ["clkX1", "clkY1", "clkX2", "clkY2"]
inPinNames = ["pSen1", "pSen2"]
outPinNames = ["pLig1", "pLig2"]
worldName = "world"

ph = ValExp $ ConVal ResetCon

testFun = presetup $ LetExp "conFun" conFun $
    AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "wgSen1", RefPat "wgRec1", RefPat "w1"]) (
        AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "wgSen2", RefPat "wgRec2", RefPat "w2"]) (
            AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "rSen1", RefPat "rRec1", RefPat "w3"]) (
                AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "rSen2", RefPat "wgRec2", RefPat "w4"]) (
                    ParExp 
                        ph
                        ph
                )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "world"))
            )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "world"))
        )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "w1"))
    )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "world"))

mainFun = presetup $ LetExp "conFun" conFun $
    AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "wgSen1", RefPat "wgRec1", RefPat "w1"]) (
        AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "wgSen2", RefPat "wgRec2", RefPat "w2"]) (
            AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "rSen1", RefPat "rRec1", RefPat "w3"]) (
                AppExp (ValExp $ MatchVal $ SingleMatch (TermPat "Triple" [RefPat "rSen2", RefPat "wgRec2", RefPat "w4"]) (
                    ParExp 
                        (AppExp (RefExp "conFun") (constructTuple "cfArgs" (map RefExp ["clkX1", "clkY1", "pSen1", "wgRec2", "rSen1", "rRec2"] ++ [ValExp tcR1, ValExp tcFalse])))
                        (AppExp (RefExp "conFun") (constructTuple "cfArgs" (map RefExp ["clkX2", "clkY2", "pSen2", "wgRec1", "rSen2", "rRec1"] ++ [ValExp tcR1, ValExp tcFalse])))
                )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "world"))
            )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "world"))
        )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "w1"))
    )) (AppExp (ValExp (ConVal OpenCon)) (RefExp "world"))

conFun = FixExp $ ValExp $ MatchVal $ 
    SingleMatch (RefPat "loop") (ValExp $ MatchVal $ SingleMatch 
        (TermPat "cfArgs" (map RefPat ["clkX", "clkY", "pSen", "pLig", "wgSen", "wgRec", "rSen", "rRec", "state", "ow"])) 
        (ValExp $ MatchVal $ MultiMatch (TermPat "R1" []) bodyR1 (
         MultiMatch (TermPat "R2" []) bodyR2 (
         MultiMatch (TermPat "G1" []) bodyG1 (
         SingleMatch (TermPat "G2" []) bodyG2)))))


bodyR1 = LetExp "pLig" (SyncExp $ SingleSync (SetSync (Left "pLig") False) (RefExp "pLig")) $ 
    patLetExp (TermPat "quad" [RefPat "rSen", RefPat "pSen", RefPat "state", RefPat "ow"]) 
        (AppExp (ValExp $ MatchVal $ 
            MultiMatch tcTruePat (constructTuple "quad" 
                [ SyncExp $ SingleSync (SendSync (Left "rSen") "tt" Nothing) (RefExp "rSen")
                , RefExp "pSen", ValExp tcR1, ValExp tcFalse]) $
            SingleMatch tcFalsePat $ AppExp 
                (SyncExp $ MultiSync (GetSync (Left "pSen") True) 
                            (constructTuple "quad" [RefExp "rSen", RefExp "pSen", ValExp tcR2, RefExp "ow"]) $ 
                        SingleSync (GetSync (Left "pSen") False) 
                            (constructTuple "quad" [RefExp "rSen", RefExp "pSen", ValExp tcR1, RefExp "ow"]))
                (SyncExp $ SingleSync (ReceiveSync (Left "pSen") "x") (constructTuple "pair" [RefExp "x", RefExp "pSen"])))
            (RefExp "ow"))
        (callLoop (map RefExp ["clkX", "clkY", "pSen'", "pLig'", "wgSen", "wgRec", "rSen'", "rRec", "state'", "ow'"]))

bodyR2 = LetExp "pLig" (SyncExp $ SingleSync (SetSync (Left "pLig") False) (RefExp "pLig")) $ 
    SyncExp $ MultiSync (SendSync (Left "rSen") "tt" Nothing) (callLoop ((map RefExp ["clkX", "clkY", "pSen", "pLig'", "wgSen", "wgRec", "rSen", "rRec"]) ++ [ValExp tcR2, RefExp "ow"])) $
              MultiSync (SendSync (Left "wgSen") "tt" Nothing) (callLoop ((map RefExp ["clkX", "clkY", "pSen", "pLig'", "wgSen", "wgRec", "rSen", "rRec"]) ++ [ValExp tcR2, RefExp "ow"])) $
              SingleSync (ReceiveSync (Left "rRec") "x") $ LetExp "clkX'" (AppExp (ValExp $ ConVal ResetCon) (RefExp "clkX")) $
                  GuardExp (callLoop (map RefExp ["clkX'", "clkY", "pSen", "pLig'", "wgSen", "wgRec", "rSen", "rRec"] ++ [ValExp tcG1, RefExp "ow"])) (ClockLCtt (Left "clkX") 15)

bodyG1 = LetExp "pLig" (SyncExp $ SingleSync (SetSync (Left "pLig") True) (RefExp "pLig")) $ 
    patLetExp (TermPat "quad" [RefPat "state'", RefPat "pSen'", RefPat "wgSen'", RefPat "clkX'"]) 
        (InvarExp (ClockLCtt (Left "clkX") 15) ["x", "y"] Map.empty 
            (SyncExp $ MultiSync (GetSync (Left "pSen") True) (constructTuple "quad" [ValExp $ tcG1, RefExp "pSen", RefExp "wgRec", RefExp "clkX"]) $
                       SingleSync (ReceiveSync (Left "wgRec") "y") (constructTuple "quad" [ValExp $ tcG2, RefExp "pSen", RefExp "wgRec", RefExp "clkX"])) 
            (LetExp "clkX'" (AppExp (ValExp $ ConVal $ ResetCon) (RefExp "clkX")) 
                (GuardExp (constructTuple "quad" [ValExp tcR1, RefExp "pSen", RefExp "wgRec", RefExp "clkX'"]) (ClockGeqCtt (Left "clkX'") 3)))) 
        (callLoop $ [loopClkX] ++ (map RefExp ["clkY", "pSen'", "pLig'", "wgSen'", "wgRec'", "rSen", "rRec", "state'", "ow"]))
            where loopClkX = ValExp $ MatchVal $ MultiMatch (TermPat "G1" []) (AppExp (ValExp $ ConVal $ ResetCon) (RefExp "clkX''")) (SingleMatch (TermPat "G2" []) (RefExp "clkX''"))

bodyG2 = LetExp "pLig" (SyncExp $ SingleSync (SetSync (Left "pLig") True) (RefExp "pLig")) $ 
    patLetExp (TermPat "Triple" [RefPat "state'", RefPat "pSen'", RefPat "clkX'"]) 
        (InvarExp (LandCtt (ClockLCtt (Left "clkX") 15) (ClockLCtt (Left "clkY") 55)) ["x"] Map.empty 
            (SyncExp $ SingleSync (GetSync (Left "pSen") True) (constructTuple "Triple" [ValExp tcG2, RefExp "pSen", RefExp "clkX"])) 
            (LetExp "clkX'" (AppExp (ValExp $ ConVal $ ResetCon) (RefExp "clkX")) $
                GuardExp (constructTuple "Triple" [ValExp tcR1, RefExp "pSen", RefExp "clkX"]) (ClockGeqCtt (Left "clkX") 3))) 
        (callLoop $ [loopClkX] ++ (map RefExp ["clkY", "pSen'", "pLig'", "wgSen", "wgRec", "rSen", "rRec", "state'", "ow"]))
            where loopClkX = AppExp (ValExp $ ConVal $ ResetCon) (RefExp "clkX''")