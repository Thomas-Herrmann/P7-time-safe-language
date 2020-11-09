{-# LANGUAGE OverloadedStrings #-}

module Main where

import Text.XML
import Ast
import Partition
import Translate
import Uppaal

ex = AppExp 
        (ValExp (MatchVal (MultiMatch (RefPat "y") (AppExp (ValExp (TermVal "Single" [])) (RefExp "y")) (SingleMatch (RefPat "x") (RefExp "x"))))) 
        (SyncExp (MultiSync (GetSync (Left "ch") True) (ValExp (TermVal "True" [])) 
                 (SingleSync (SetSync (Left "ch2") True) (ValExp (TermVal "False" [])))))

ex' = AppExp
        (ValExp (MatchVal (SingleMatch (RefPat "x") (RefExp "x"))))
        (ValExp (TermVal "True" []))

tem = Template { temName = "Test Template"
               , temLocations = [ Location "id0" [] (Just "hehe")
                                , Location "id1" [] (Just "xd")]
               , temTransitions = [Transition "id0" "id1" []]
               , temDecls = ["These are template declarations"]
               , temInit = "id0"}

sys = System { sysDecls = [ "chan pSen, pSen2, rSen, pLig, wgSen, wgRec, rRec;"
                          , "bool pSenval = false, pSenval2 = false;"
                          , "bool ow = false, ow2 = false;"]
             , sysTemplates = [tem]
             , sysSystemDecls = ["This is a system declaration"]
             , sysQueries = [Query "This is a query" "This is a comment"] }


main :: IO ()
--main = do 
--    print $ show ex
--    print $ show (partition ex 0)
--main = Text.XML.writeFile def "test.xml" $ systemToXML sys
main = case translate (LetExp "x" (ValExp (ConVal OpenCon)) (RefExp "x")) [] [] [] "test" of
        Nothing  -> print "failure"
        Just sys -> Text.XML.writeFile def "test.xml" $ systemToXML sys