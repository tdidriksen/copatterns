module Findus where

import Parser
import TypeChecker
import System.Environment
import System.IO  
import Control.Monad
import Data.Char(toUpper)


main :: IO ()
main = do 
        args <- getArgs
        inh <- openFile (args !! 0) ReadMode
        contents <- hGetContents inh
        case readExpr contents of
          Left err -> putStr $ show err
          Right e  -> case checkRoot e of
                        Left err -> putStr $ show err
                        Right te -> putStr "Done."
        putStr "\n"
        hClose inh