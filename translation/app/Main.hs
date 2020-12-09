{-# LANGUAGE OverloadedStrings #-}

module Main where

import Text.XML
import Ast
import Translate
import Uppaal
import System.IO
import Data.Functor
import Data.Text as Text

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering

    inFileName <- putStr "Input file (default input.txt): " >> getLine >>= (\s -> return $ if s == "" then "input.txt" else s)
    outFileName <- putStr "Output file (default output.xml): " >> getLine >>= (\s -> return $ if s == "" then "output.xml" else s)
    usePruning <- putStr "Use pruning? (y/n) (default y): " >> getLine >>= (\s -> return $ s == "y" || s == "")
    forceDelays <- putStr "Force delays? (y/n) (default y): " >> getLine >>= (\s -> return $ s == "y" || s == "")
    delays <- 
        if forceDelays
        then do 
            minD <- putStr "Min (default 20): " >> getLine >>= (\s -> return $ if s == "" then "20" else s) <&> (read :: String -> Integer)
            maxD <- putStr "Max (default 50): " >> getLine >>= (\s -> return $ if s == "" then "20" else s) <&> (read :: String -> Integer)
            return $ Just (minD, maxD)
        else return Nothing
    
    inHandle <- openFile inFileName ReadMode
    clockNames <- hGetLine inHandle <&> Prelude.filter (/= ' ') <&> Text.pack <&> Text.splitOn "," <&> Prelude.map Text.unpack
    inPinNames <- hGetLine inHandle <&> Prelude.filter (/= ' ') <&> Text.pack <&> Text.splitOn "," <&> Prelude.map Text.unpack
    outPinNames <- hGetLine inHandle <&> Prelude.filter (/= ' ') <&> Text.pack <&> Text.splitOn "," <&> Prelude.map Text.unpack
    sendChannelNames <- hGetLine inHandle <&> Prelude.filter (/= ' ') <&> Text.pack <&> Text.splitOn "," <&> Prelude.map Text.unpack
    recvChannelNames <- hGetLine inHandle <&> Prelude.filter (/= ' ') <&> Text.pack <&> Text.splitOn "," <&> Prelude.map Text.unpack
    program <- hGetContents inHandle <&> (read :: String -> Exp)


    maybe <- translate usePruning delays program clockNames inPinNames outPinNames (Prelude.zip sendChannelNames recvChannelNames)
    case maybe of
        Nothing  -> putStrLn "Failed to translate program"
        Just sys -> Text.XML.writeFile def outFileName (systemToXML sys) >> putStrLn "Success"