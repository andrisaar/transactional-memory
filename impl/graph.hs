#!/usr/bin/runhugs -98

module Main (Main.main) where

import Language
import TM
import SimpleTM
import EagerTM
import LazyTM
import qualified Data.List as List

edgeColour :: String -> String
edgeColour s | "commit" `List.isInfixOf` s = "green"
             | "rollback" `List.isInfixOf` s = "red"
	     | "atomic" `List.isInfixOf` s = "blue"
	     | otherwise = "black"

graphstep :: TM a => [a] -> ([a], [(a, a, String)]) -> ([a], [(a, a, String)])
graphstep []         result         = result
graphstep (cfg:cfgs) (nodes, edges) = graphstep (cfgs ++ newNodes) (nodes ++ newNodes, edges ++ newEdges)
  where allNodes = steps cfg
        newNodes = filter (flip notElem $ nodes) $ map fst allNodes
	newEdges = filter (flip notElem $ edges) $ map (\(x, l) -> (cfg, x, l)) allNodes

graphEval :: TM a => a -> String
graphEval  s = "digraph Program {\n\tnode [shape=ellipse];\n" ++
		concatMap (\x -> "\tnode" ++ (show x) ++ " [ label = \"" ++ {- concatMap (\x -> if x == '\"' then "\\\"" else if x == '\n' then "\\n\\\n" else [x]) (show $ nodes !! x) ++ -} "\" ];\n") [0 .. length nodes - 1] ++
		"\n\n" ++
		concatMap (\(x, y, l) -> "\tnode" ++ (show $ maybe (error "Node not found") id $ List.elemIndex x nodes) ++ " -> node" ++ (show $ maybe (error "Node not found") id $ List.elemIndex y nodes) ++ " [ label = \"" ++ l ++ "\" color = \"" ++ (edgeColour l)++ "\"]; \n") edges ++
		"}"
  where (nodes, edges) = graphstep [s] ([s], [])

main = TM.main f
  where f :: String -> ThreadStore -> IO ()
        f "eager"  ts = putStrLn $ graphEval $ (TM.init ts :: ECfg)
        f "simple" ts = putStrLn $ graphEval $ (TM.init ts :: SCfg)
        f "lazy"   ts = putStrLn $ graphEval $ (TM.init ts :: LCfg)
        f e        _  = fail $ "Unknown TM engine: " ++ e
