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

--testNew = FixExp (ValExp (MatchVal (SingleMatch (RefPat "f")
--                ())))

testE2'' = InvarExp (ClockLeqCtt (Left "clk1") 25) [] Map.empty testE2 $ (ValExp (ConVal ResetCon))

main :: IO ()
main = do
   print $ show Example.mainFun
   case translate Example.mainFun Example.clockNames Example.inPinNames Example.outPinNames Example.worldName of
      Nothing  -> putStrLn "failure"
      Just sys -> Text.XML.writeFile def "test.xml" $ systemToXML sys