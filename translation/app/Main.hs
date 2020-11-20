{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Map as Map
import Data.Set as Set
import Text.XML
import Ast
import Partition
import Translate
import Uppaal
import Example

--ex = AppExp 
--        (ValExp (MatchVal (MultiMatch (RefPat "y") (AppExp (ValExp (TermVal "Single" [])) (RefExp "y")) (SingleMatch (RefPat "x") (RefExp "x"))))) 
--        (SyncExp (MultiSync (GetSync (Left "ch") True) (ValExp (TermVal "True" [])) 
--                 (SingleSync (SetSync (Left "ch2") True) (ValExp (TermVal "False" [])))))
--
--ex' = AppExp
--        (ValExp (MatchVal (SingleMatch (RefPat "x") (RefExp "x"))))
--        (ValExp (TermVal "True" []))
--
--tem = Template { temName = "Test Template"
--               , temLocations = [ Location "id0" [] (Just "hehe")
--                                , Location "id1" [] (Just "xd")]
--               , temTransitions = [Transition "id0" "id1" []]
--               , temDecls = ["These are template declarations"]
--               , temInit = "id0"}
--
--sys = System { sysDecls = [ "chan pSen, pSen2, rSen, pLig, wgSen, wgRec, rRec;"
--                          , "bool pSenval = false, pSenval2 = false;"
--                          , "bool ow = false, ow2 = false;"]
--             , sysTemplates = [tem]
--             , sysSystemDecls = ["This is a system declaration"]
--             , sysQueries = [Query "This is a query" "This is a comment"] }

testE = (LetExp "x" 
                (GuardExp (RefExp "clk1") (ClockLCtt (Left "clk1") 323)) 
                (AppExp 
                        (ValExp (ConVal ResetCon)) 
                        (RefExp "x")))

testE2 = (AppExp 
                (ValExp (MatchVal (SingleMatch 
                        (TermPat "Triple" [RefPat "ch", RefPat "ch'", RefPat "w'"]) 
                        ((ParExp 
                                (SyncExp (SingleSync (ReceiveSync (Left "ch'") "res") (ValExp (ConVal ResetCon)))) 
                                (SyncExp (SingleSync (SendSync (Left "ch") "clk1" Nothing) (ValExp (ConVal ResetCon))))))))) 
                (AppExp 
                        (ValExp (ConVal OpenCon)) 
                        (RefExp "w")))

testE2'' = InvarExp (ClockLeqCtt (Left "clk1") 25) [] Map.empty testE2 (ValExp (ConVal ResetCon))


number n | n <= 0    = TermVal "Null" []
         | otherwise = TermVal "Succ" [number $ n - 1]

testNew = AppExp
                (FixExp (ValExp (MatchVal (SingleMatch (RefPat "plus") 
                        (ValExp (MatchVal (MultiMatch (TermPat "Pair" [TermPat "Succ" [RefPat "one"], RefPat "two"]) 
                                 (AppExp 
                                                (RefExp "plus") 
                                                (AppExp 
                                                        (AppExp (ValExp (TermVal "Pair" [])) (RefExp "one")) 
                                                        (AppExp (ValExp (TermVal "Succ" [])) (RefExp "two"))))
                                (SingleMatch (TermPat "Pair" [RefPat "one", RefPat "two"])
                                        (RefExp "two")))))))))
                (ValExp (TermVal "Pair" [number 5, number 5]))


testNew' = AppExp
                (FixExp (ValExp (MatchVal (SingleMatch (RefPat "swap") 
                        (ValExp (MatchVal (MultiMatch (RefPat "one")
                                (AppExp (RefExp "swap") (RefExp "one"))
                                (SingleMatch (RefPat "two")
                                        (ValExp (TermVal "Green" []))))))))))
                (ValExp (TermVal "Blue" []))

invarTest = InvarExp (LandCtt (ClockLCtt (Left "clkX2") 15) (ClockLCtt (Left "clkX1") 55)) [] Map.empty
                (ValExp (ConVal ResetCon))
                (ValExp (ConVal ResetCon))


main :: IO ()
main = do
   maybe <- translate True Example.mainFun Example.clockNames Example.inPinNames Example.outPinNames Example.worldName
   case maybe of
      Nothing  -> putStrLn "failure"
      Just sys -> Text.XML.writeFile def "example.xml" $ systemToXML sys