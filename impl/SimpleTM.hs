
module SimpleTM (SCfg) where
import Language
import TM

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

data SCfg = SCfg { 
    threadStore :: ThreadStore, 
    store :: Store
}
  deriving Eq

instance Show SCfg where
  show (SCfg ts s) = 
    "Threads:\n" ++
      (unlines $ zipWith (\x y -> "  T" ++ (show x) ++ ": " ++ (show y)) (iterate (+1) 0) ts) ++
    "Store:\n" ++
      (unlines $ Map.foldWithKey (\k a b -> b ++ ["  " ++ k ++ "=" ++ show a]) [] s)

--
-- Arithmetic expressions
--

aexp :: AExp -> Store -> Integer
aexp (N n)      _ = n
aexp (V v)      s = Map.findWithDefault 0 v s
aexp (a1 :+ a2) s = aexp a1 s + aexp a2 s
aexp (a1 :- a2) s = aexp a1 s - aexp a2 s
aexp (a1 :* a2) s = aexp a1 s * aexp a2 s

--
-- Boolean expressions
--

bexp :: BExp -> Store -> Bool
bexp TT          s = True
bexp FF          s = False
bexp (Not b)     s = not $ bexp b s
bexp (a1 :== a2) s = aexp a1 s == aexp a2 s
bexp (a1 :<= a2) s = aexp a1 s <= aexp a2 s
bexp (b1 :&& b2) s = bexp b1 s && bexp b2 s
bexp (b1 :|| b2) s = bexp b1 s || bexp b2 s

transactional :: ThreadStore -> Maybe ThreadID
transactional ts = transactional' 0
  where transactional' n | n == length ts = Nothing
                         | otherwise      = case ts !! n of
                                              Just (InTx _ _) -> Just $ toInteger n
                                              _               -> transactional' (n+1)

instance TM SCfg where
  init ts = SCfg ts Map.empty

  -- if any of the threads is in a transaction we can only take one step with that thread
  step cfg n = if maybe True (== n) (transactional $ threadStore cfg) then
                  do t <- threadStore cfg !!? n
                     stmt <- t
                     (cfg', stmt', l) <- step' cfg False stmt
                     return (cfg' { threadStore = updt n stmt' $ threadStore cfg' }, "T" ++ (show n) ++ "/" ++ l)
               else fail ""

  steps cfg = catMaybes . map (step cfg) . availableThreads . threadStore $ cfg

  isTerminal cfg = all isNothing . threadStore $ cfg

step' :: SCfg -> Bool -> Stmt -> Maybe (SCfg, Maybe Stmt, String)

step' cfg _     (While b stmt)      = return (cfg, Just $ If b (stmt :\ (While b stmt)) Skip, "while")

step' cfg b     (stmt1 :\ stmt2)    = do (cfg', stmt', s) <- step' cfg b stmt1
                                         return (cfg', Just $ maybe stmt2 (:\ stmt2) stmt', s)

step' cfg _     Skip                = return (cfg, Nothing, "skip")

step' cfg False (Spawn stmts)       = return (cfg { threadStore = (threadStore cfg ++ map Just stmts) }, Nothing, "spawn")

step' cfg _     (If b stm1 stm2)    = return (cfg, Just $ if bexp b (store cfg) then stm1 else stm2, "if")

step' cfg _     (v := a)            = return (cfg { store = Map.insert v (aexp a $ store cfg) (store cfg) }, Nothing, v ++ " := " ++ (show (aexp a $ store cfg)))

step' ctx _     (Atomic stmt)       = return (ctx, Just $ InTx stmt (Just stmt), "atomic") 

step' cfg b     (InTx s1 (Just s2)) = do (cfg', stmt', l) <- step' cfg True s2
                                         return (cfg', Just $ InTx s1 stmt', "tx/" ++ l)

step' cfg _     (InTx s1 Nothing)   = return (cfg, Nothing, "commit")


