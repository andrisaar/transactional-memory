
module TM (TM, init, step, steps, isTerminal, main) where

import Prelude hiding (init)
import Language
import Parser
import qualified Data.List as List
import System
import IO

class (Eq a, Show a) => TM a where
  init :: ThreadStore -> a
  step :: a -> Integer -> Maybe (a, String)
  steps :: a -> [(a, String)]
  isTerminal :: a -> Bool

--
--
--

eval :: (String -> ThreadStore -> IO ()) -> String -> String -> IO ()
eval f engine path = do h <- openFile path ReadMode
                        contents <- hGetContents h
	                case parseProgram path contents of
	                  Left e -> putStrLn $ show e
	  	          Right stmt -> f engine (singleThreadStore stmt)
                        hClose h


main :: (String -> ThreadStore -> IO ()) -> IO ()
main f = do args <- getArgs
            if length args < 2 then do { name <- getProgName; putStrLn $ "Usage: " ++ name ++ " [engine] [file] ..."; exitWith ExitSuccess } else return ()
            let (engine : files) = args
            mapM_ (eval f engine) files

