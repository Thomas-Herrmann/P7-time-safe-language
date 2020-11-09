module Main where

import Ast
import Partition
import Translate


ex = AppExp 
        (ValExp (MatchVal (MultiMatch (RefPat "y") (AppExp (ValExp (TermVal "Single" [])) (RefExp "y")) (SingleMatch (RefPat "x") (RefExp "x"))))) 
        (SyncExp (MultiSync (GetSync (Left "ch") True) (ValExp (TermVal "True" [])) 
                 (SingleSync (SetSync (Left "ch2") True) (ValExp (TermVal "False" [])))))

ex' = AppExp
        (ValExp (MatchVal (SingleMatch (RefPat "x") (RefExp "x"))))
        (ValExp (TermVal "True" []))


main :: IO ()
main = do 
    print $ show ex
    print $ show (partition ex 0)
