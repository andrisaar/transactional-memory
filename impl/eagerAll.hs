#!/usr/bin/runhugs -98

module Main (Main.main) where

import Parser
import Language
import TM
import EagerTM
import SimpleTM
import LazyTM

bdstep :: TM a => [a] -> [a] -> [a]
bdstep []         states = states
bdstep (cfg:cfgs) states = bdstep (cfgs ++ results) (results ++ states)
  where results = filter (flip notElem $ states) $ map fst $ steps cfg

bdEval :: TM a => a -> [a]
bdEval init = bdstep [init] [init]

main = TM.main f 
  where f :: String -> ThreadStore -> IO ()
        f "eager"  ts = putStrLn $ unlines $ map show $ filter isTerminal $ bdEval (TM.init ts :: ECfg)
        f "simple" ts = putStrLn $ unlines $ map show $ filter isTerminal $ bdEval (TM.init ts :: SCfg)
        f "lazy"   ts = putStrLn $ unlines $ map show $ filter isTerminal $ bdEval (TM.init ts :: LCfg)
        f e        _  = fail $ "Unknown TM engine: " ++ e
