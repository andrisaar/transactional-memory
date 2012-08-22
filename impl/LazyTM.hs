
module LazyTM (LCfg) where
import Language
import TM

import Prelude hiding (reads)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

type ReadSet = Set Var

data TxCtx = TxCtx {
    reads :: Store,
    writes :: Store,
    lockSnapshot :: Integer
}
  deriving (Eq, Show)

emptyCtx :: Integer -> TxCtx
emptyCtx lock = TxCtx Map.empty Map.empty lock

data LCfg = LCfg { 
    threadStore :: ThreadStore, 
    store :: Store,
    globalLock :: Integer,
    txCtx :: Map ThreadID TxCtx
}
  deriving Eq

instance Show LCfg where
  show (LCfg ts s lck ctx) = 
    "Threads:\n" ++
      (unlines $ zipWith (\x y -> "  T" ++ (show x) ++ ": " ++ (show y)) (iterate (+1) 0) ts) ++
    "Store:\n" ++
      (unlines $ Map.foldWithKey (\k a b -> b ++ ["  " ++ k ++ "=" ++ show a]) [] s) ++
    "Global lock:\n" ++
      "  " ++ (show lck) ++ 
    "Transaction contexts:\n" ++
      (unlines $ Map.foldWithKey (\k a b -> b ++ ["  " ++ show k ++ ": " ++ show a]) [] ctx)

instance TM LCfg where
  init ts = LCfg ts Map.empty 0 Map.empty

  step cfg n = do t <- threadStore cfg !!? n
                  stmt <- t
                  (cfg', stmt', _, l) <- step' cfg Nothing n stmt
                  return (cfg' { threadStore = updt n stmt' $ threadStore cfg' }, "T" ++ (show n) ++ "/" ++ l)

  steps cfg = catMaybes . map (step cfg) . availableThreads . threadStore $ cfg

  isTerminal cfg = all isNothing . threadStore $ cfg


--
-- Arithmetic expressions
--

aexp' :: MonadState ReadSet a => AExp -> Store -> Store -> a Integer
aexp' (N n)      _ _ = return n
aexp' (V v)      s w = case Map.lookup v w of
                         Just val -> return val
                         Nothing  -> do vals <- get
                                        put $ Set.insert v vals 
                                        return $ Map.findWithDefault 0 v s
aexp' (a1 :+ a2) s w = do z1 <- aexp' a1 s w
                          z2 <- aexp' a2 s w
                          return $ z1 + z2
aexp' (a1 :- a2) s w = do z1 <- aexp' a1 s w
                          z2 <- aexp' a2 s w
                          return $ z1 - z2
aexp' (a1 :* a2) s w = do z1 <- aexp' a1 s w
                          z2 <- aexp' a2 s w
                          return $ z1 * z2

aexp :: AExp -> Store -> Store -> (Integer, ReadSet)
aexp a s w = runState (aexp' a s w) Set.empty

--
-- Boolean expressions
--

bexp' :: MonadState ReadSet a =>  BExp -> Store -> Store -> a Bool
bexp' TT          _ _ = return True
bexp' FF          _ _ = return False
bexp' (Not b)     s w = do z <- bexp' b s w
                           return $ not z
bexp' (a1 :== a2) s w = do z1 <- aexp' a1 s w
                           z2 <- aexp' a2 s w
                           return $ z1 == z2
bexp' (a1 :<= a2) s w = do z1 <- aexp' a1 s w
                           z2 <- aexp' a2 s w
                           return $ z1 <= z2
bexp' (b1 :&& b2) s w = do z1 <- bexp' b1 s w
                           z2 <- bexp' b2 s w
			   return $ z1 && z2
bexp' (b1 :|| b2) s w = do z1 <- bexp' b1 s w
                           z2 <- bexp' b2 s w
			   return $ z1 || z2

bexp :: BExp -> Store -> Store -> (Bool, ReadSet)
bexp b s w = runState (bexp' b s w) Set.empty

isValid :: TxCtx -> LCfg -> Bool
isValid ctx cfg | (lockSnapshot ctx) == (globalLock cfg) = True
                | otherwise                              = readsConsistent (store cfg) (reads ctx)
  where readsConsistent :: Store -> Store -> Bool
        readsConsistent store reads = Map.foldWithKey (\k v b -> v == (Map.findWithDefault 0 k store) && b) True reads

validate :: TxCtx -> LCfg -> Maybe TxCtx
validate ctx cfg | (lockSnapshot ctx) == (globalLock cfg) = return ctx
                 | isValid ctx cfg                        = return ctx { lockSnapshot = (globalLock cfg) }
                 | otherwise                              = fail ""


step' :: LCfg -> Maybe TxCtx -> ThreadID -> Stmt -> Maybe (LCfg, Maybe Stmt, Maybe TxCtx, String)


step' cfg ctx        _ (While b stmt)     = return (cfg, Just $ If b (stmt :\ (While b stmt)) Skip, ctx, "while")
step' cfg ctx        n (stmt1 :\ stmt2)   = do (cfg', stmt', ctx', s) <- step' cfg ctx n stmt1
                                               return (cfg', Just $ maybe stmt2 (:\ stmt2) stmt', ctx', s)
step' cfg ctx        _ Skip               = return (cfg, Nothing, ctx, "skip")
step' cfg Nothing    _ (Spawn stmts)      = return (cfg { threadStore = (threadStore cfg ++ map Just stmts) }, Nothing, Nothing, "spawn")


step' cfg Nothing    _ (If b stm1 stm2)   = return (cfg, Just $ if z then stm1 else stm2, Nothing, "if")
  where (z, _) = bexp b (store cfg) Map.empty

step' cfg (Just ctx) n (If b stm1 stm2)   = do ctx'' <- validate ctx' cfg
                                               return (cfg, Just $ if z then stm1 else stm2, Just ctx'', "if")
  where (z, rs) = bexp b (store cfg) (writes ctx)
        ctx' = ctx { reads = Set.fold (\k rs -> Map.insert k (Map.findWithDefault 0 k (store cfg)) rs) (reads ctx) rs }


step' cfg Nothing    _ (v := a)           = return (cfg', Nothing, Nothing, v ++ " := " ++ (show z))
  where (z, _) = aexp a (store cfg) Map.empty
        cfg' = cfg { store = Map.insert v z (store cfg),
                     globalLock = (globalLock cfg) + 1
                   }

step' cfg (Just ctx) n (v := a)           = do ctx'' <- validate ctx' cfg
                                               return (cfg, Nothing, Just ctx'', v ++ " := " ++ (show z))
  where (z, rs) = aexp a (store cfg) (writes ctx)
        ctx' = ctx { reads = Set.fold (\k rs -> Map.insert k (Map.findWithDefault 0 k (store cfg)) rs) (reads ctx) rs,
                     writes = Map.insert v z (writes ctx)}


step' cfg Nothing    n (Atomic stmt)     = return (cfg {txCtx = Map.insert n (emptyCtx $ globalLock cfg) $ txCtx cfg }, Just $ InTx stmt (Just stmt), Nothing, "atomic")
step' cfg (Just ctx) n (Atomic stmt)     = return (cfg, Just stmt, Just ctx, "atomic")


-- stepping in a transaction
step' cfg Nothing    n (InTx s1 (Just s2)) = 
    case step' cfg (Just ctx) n s2 of
      Just (cfg', stmt', ctx', l) -> return (cfg' { txCtx = Map.insert n (maybe (error "No context!") id ctx') (txCtx cfg) }, Just $ InTx s1 stmt', Nothing, "tx/" ++ l)
      Nothing                     -> return (cfg { txCtx = Map.delete n (txCtx cfg) }, Just $ Atomic s1, Nothing, "rollback")
  where ctx = (txCtx cfg) Map.! n
                                           
step' cfg (Just ctx) n (InTx s1 (Just s2)) = do (cfg', s2', ctx', l) <- step' cfg (Just ctx) n s2
                                                return (cfg', Just $ InTx s1 s2', ctx', l)

-- ending a transaction
step' cfg Nothing    n (InTx s1 Nothing) | isValid ctx cfg = return (cfg', Nothing, Nothing, "commit")
                                         | otherwise       = return (cfg { txCtx = Map.delete n (txCtx cfg) }, Just $ Atomic s1, Nothing, "rollback")
  where ctx = (txCtx cfg) Map.! n
        cfg' = cfg { store = Map.foldWithKey Map.insert (store cfg) (writes ctx),
                     txCtx = Map.delete n (txCtx cfg),
                     globalLock = (globalLock cfg) + 1
                   }

step' cfg (Just ctx) n (InTx s1 Nothing) = return (cfg, Nothing, Just ctx, "commit")
