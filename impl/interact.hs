#!/usr/bin/runhugs -98

module Main (Main.main) where

import Language
import TM
import EagerTM
import SimpleTM
import LazyTM

interactEvalLoop :: TM a => a -> IO ()
interactEvalLoop cfg = do putStr "> "
                          n <- getLine
			  let cfg' = step cfg $ read n
                          cfg'' <- do case cfg' of
                                        Just (cfg'', a) -> do putStrLn $ a
                                                              return cfg''
                                        _               -> return cfg
                          putStrLn $ show cfg''
                          interactEvalLoop cfg''

interactEval :: TM a => a -> IO ()
interactEval cfg = do putStrLn $ show cfg
                      interactEvalLoop cfg


main = TM.main f
  where f :: String -> ThreadStore -> IO ()
        f "eager"  ts = interactEval $ (TM.init ts :: ECfg)
        f "simple" ts = interactEval $ (TM.init ts :: SCfg)
        f "lazy"   ts = interactEval $ (TM.init ts :: LCfg)
        f e        _  = fail $ "Unknown TM engine: " ++ e
