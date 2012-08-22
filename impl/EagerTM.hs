
module EagerTM (ECfg) where
import Language
import TM

import Data.Maybe
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

newtype TxID = TX (ThreadID, Integer)

instance Ord TxID where
  TX (i, n) <= TX (j, m) = i <= n || n <= m

-- our very own partial order
TX (i, n) <=% TX (j, m) = i == j && n <= m

instance Eq TxID where
  TX (i, n) == TX (j, m) = i == j && n == m

instance Show TxID where
  show (TX (i, n)) = "(" ++ show i ++ ", " ++ show n ++ ")"

isNonTx :: TxID -> Bool
isNonTx (TX (_, 0)) = True
isNonTx _           = False

succTx :: TxID -> TxID
succTx (TX (n, m)) = TX (n, m+1)

predTx :: TxID -> TxID
predTx (TX (n, 0)) = TX (n, 0)
predTx (TX (n, m)) = TX (n, m-1)

initTx :: Integer -> TxID
initTx n = TX (n, 0)

type VarOwn = Map Var (Set TxID, Maybe TxID)
type ReadSet = Set Var

data TxCtx = TxCtx {
    valid :: Bool,
    history :: Map Var Integer,
    readSet :: ReadSet
}
  deriving (Eq, Show)

data ECfg = ECfg { 
    threadStore :: ThreadStore, 
    store :: Store, 
    varOwn :: VarOwn,
    txCtx :: Map TxID TxCtx
}
  deriving Eq

instance Show ECfg where
  show (ECfg ts s vo ctx) = 
    "Threads:\n" ++
      (unlines $ zipWith (\x y -> "  T" ++ (show x) ++ ": " ++ (show y)) (iterate (+1) 0) ts) ++
    "Store:\n" ++
      (unlines $ Map.foldWithKey (\k a b -> b ++ ["  " ++ k ++ "=" ++ show a]) [] s) ++
    "Ownership:\n" ++
      (unlines $ Map.foldWithKey (\k a b -> b ++ ["  " ++ k ++ "=" ++ show a]) [] (Map.filter (/= (Set.empty, Nothing)) vo)) ++
    "Transaction contexts:\n" ++
      (unlines $ Map.foldWithKey (\k a b -> b ++ ["  " ++ show k ++ ": " ++ show a]) [] ctx)

emptyTxCtx :: TxCtx
emptyTxCtx = TxCtx True Map.empty Set.empty

getTxCtx' :: TxID -> Map TxID TxCtx -> TxCtx
getTxCtx' txid ctxs = Map.findWithDefault emptyTxCtx txid ctxs
getTxCtx :: TxID -> ECfg -> TxCtx
getTxCtx txid cfg = getTxCtx' txid (txCtx cfg)
--
-- Utility functions
--
--

hasReadBefore :: ECfg -> TxID -> Var -> Bool
hasReadBefore cfg txid var =
  Map.foldWithKey (\txid' ctx b -> if txid' <=% txid then b || Set.member var (readSet ctx) else b) False (txCtx cfg)

hasNotReadBefore :: ECfg -> TxID -> Var -> Bool
hasNotReadBefore cfg txid var = not $ hasReadBefore cfg txid var

acquireRead' :: TxID -> Var -> VarOwn -> VarOwn
acquireRead' txid k vo = Map.insert k (Set.insert txid r, w) vo
  where (r, w) = Map.findWithDefault (Set.empty, Nothing) k vo

acquireRead :: ReadSet -> TxID -> VarOwn -> VarOwn
acquireRead rs txid vo | isNonTx txid = vo 
                       | otherwise    = Set.fold (acquireRead' txid) vo rs

acquireWrite :: TxID -> Var -> VarOwn -> Maybe (VarOwn, Set TxID)
acquireWrite txid v vo | isNonTx txid = case Map.lookup v vo of
                                          Nothing               -> return (vo, Set.empty)
                                          Just (rs, Nothing)    -> return (Map.insert v (Set.empty, Nothing) vo, rs)
                                          Just (rs, Just txid') -> return (Map.insert v (Set.empty, Nothing) vo, Set.insert txid' rs)
                       | v `Map.member` vo = case vo Map.! v of
                                              (rs, Nothing)   -> return (Map.insert v (Set.empty, Just txid) vo, rs)
                                              (rs, Just txid') -> if txid' <=% txid then
                                                                    return (Map.insert v (Set.empty, Just txid') vo, rs)
                                                                  else
                                                                    fail ""
                       | otherwise         = return (Map.insert v (Set.empty, Just txid) vo, Set.empty)

hasWrite :: TxID -> Var -> VarOwn -> Bool
hasWrite txid v vo | v `Map.member` vo = case vo Map.! v of
                                          (_, Nothing)    -> False
                                          (_, Just txid') -> txid' <=% txid
                   | otherwise = False

invalidateTxs :: Set TxID -> Map TxID TxCtx -> Map TxID TxCtx
invalidateTxs txs ctxs = 
  Map.mapWithKey (\k ctx -> if Set.fold (\txid b -> txid <=% k || b) False txs then ctx { valid = False } else ctx) ctxs

dropLocks :: TxID -> VarOwn -> VarOwn
dropLocks txid vo = Map.map (\(r, w) -> (Set.delete txid r, maybe Nothing (\txid' -> if txid == txid' then Nothing else Just txid') w)) vo

locksToParent :: TxID -> VarOwn -> VarOwn
locksToParent txid vo | isNonTx parentId = Map.map (\(r, w) -> (Set.filter (\txid' -> not $ txid == txid') r, maybe Nothing (\txid' -> if txid == txid' then Nothing else Just txid') w)) vo
                      | otherwise = Map.map (\(r, w) -> (Set.map f r, maybe Nothing (Just . f) w)) vo
  where parentId = predTx txid
        f txid' = if txid == txid' then parentId else txid'

mergeParent :: TxID -> Map TxID TxCtx -> Map TxID TxCtx
mergeParent txid ctxs | isNonTx parentId = Map.delete txid ctxs
                      | otherwise        = Map.insert parentId (parentCtx { history = (history parentCtx) `Map.union` (history myCtx), readSet = (readSet parentCtx) `Set.union` (readSet myCtx) }) $ Map.delete txid ctxs
  where parentId = predTx txid
        myCtx = getTxCtx' txid ctxs
        parentCtx = getTxCtx' parentId ctxs

--
-- Arithmetic expressions
--

aexp' :: MonadState ReadSet a => AExp -> Store -> a Integer
aexp' (N n)      _ = return n
aexp' (V v)      s = do vals <- get
                        put $ Set.insert v vals 
                        return $ Map.findWithDefault 0 v s
aexp' (a1 :+ a2) s = do z1 <- aexp' a1 s
                        z2 <- aexp' a2 s
                        return $ z1 + z2
aexp' (a1 :- a2) s = do z1 <- aexp' a1 s
                        z2 <- aexp' a2 s
                        return $ z1 - z2
aexp' (a1 :* a2) s = do z1 <- aexp' a1 s
                        z2 <- aexp' a2 s
                        return $ z1 * z2

aexp :: AExp -> Store -> (Integer, ReadSet)
aexp a s = runState (aexp' a s) Set.empty

--
-- Boolean expressions
--

bexp' :: MonadState ReadSet a =>  BExp -> Store -> a Bool
bexp' TT          s = return True
bexp' FF          s = return False
bexp' (Not b)     s = do z <- bexp' b s
                         return $ not z
bexp' (a1 :== a2) s = do z1 <- aexp' a1 s
                         z2 <- aexp' a2 s
                         return $ z1 == z2
bexp' (a1 :<= a2) s = do z1 <- aexp' a1 s
                         z2 <- aexp' a2 s
                         return $ z1 <= z2
bexp' (b1 :&& b2) s = do z1 <- bexp' b1 s
                         z2 <- bexp' b2 s
			 return $ z1 && z2
bexp' (b1 :|| b2) s = do z1 <- bexp' b1 s
                         z2 <- bexp' b2 s
			 return $ z1 || z2

bexp :: BExp -> Store -> (Bool, ReadSet)
bexp b s = runState (bexp' b s) Set.empty

--
--
--

instance TM ECfg where
  -- empty store, nobody has any ownerships, no transactions yet
  init ts = ECfg ts Map.empty Map.empty Map.empty

  step cfg n = do t <- threadStore cfg !!? n
                  stmt <- t
                  (cfg', stmt', l) <- step' cfg (initTx n) stmt
                  return (cfg' { threadStore = updt n stmt' $ threadStore cfg' }, "T" ++ (show n) ++ "/" ++ l)

  steps cfg = catMaybes . map (step cfg) . availableThreads . threadStore $ cfg

  isTerminal cfg = all isNothing . threadStore $ cfg


step' :: ECfg -> TxID -> Stmt -> Maybe (ECfg, Maybe Stmt, String)

-- BORING STUFF
step' cfg txid (While b stmt)     = return (cfg, Just $ If b (stmt :\ (While b stmt)) Skip, "while")
step' cfg txid (stmt1 :\ stmt2)   = do (cfg', stmt', s) <- step' cfg txid stmt1
                                       return (cfg', Just $ maybe stmt2 (:\ stmt2) stmt', s)
step' cfg _     Skip              = return (cfg, Nothing, "skip")
step' cfg txid (Spawn stmts)      | isNonTx txid = 
  return (cfg { threadStore = (threadStore cfg ++ map Just stmts) }, Nothing, "spawn")

-- IF STATEMENT (chance of variables being read)
-- a) we expect that we are consistent (ie we still hold a read lock for everything in our read set)
-- b) if we read any new variables, acquire the read lock for them
step' cfg txid (If b stm1 stm2)   = return (if isNonTx txid then cfg else cfg', Just $ if z then stm1 else stm2, "if")
  where (z, rs) = bexp b (store cfg)
        newReadSet = Set.filter (hasNotReadBefore cfg txid) rs
        cfg' = cfg { varOwn = acquireRead newReadSet txid (varOwn cfg),
                     txCtx = Map.insertWith (\_ ctx -> ctx { readSet = (readSet ctx `Set.union` newReadSet) } ) txid emptyTxCtx (txCtx cfg)
                   }

-- ASSIGNMENT
-- a) again, we assume that we are consistent
-- b) if we read some new variable, acquire a read lock on it
-- c) if we don't have the write lock for the var we are assigning to, acquire it
-- d) remove any read locks that may exist for the variable, except those held by our parents, and invalidate them
step' cfg txid (v := a)           = do (vo, rs') <- acquireWrite txid v (varOwn cfg)
                                       return (cfg { varOwn = acquireRead newReadSet txid vo, 
                                                     txCtx = (if isNonTx txid then id else Map.insertWith f txid emptyTxCtx) $ invalidateTxs (Set.filter (\txid' -> not $ txid' <=% txid) rs') (txCtx cfg),
                                                     store = Map.insert v z (store cfg)
                                                   }, Nothing, v ++ " := " ++ (show z))
  where (z, rs) = aexp a (store cfg)
        newReadSet = Set.filter (hasNotReadBefore cfg txid) rs
        f _ ctx = ctx { readSet = newReadSet `Set.union`readSet ctx,
                        history = Map.insertWith (curry snd) v (Map.findWithDefault 0 v $ store cfg) $ history ctx
                      }

-- starting a transaction
step' ctx txid (Atomic stmt)      = return (ctx, Just $ InTx stmt (Just stmt), "atomic")

-- stepping in a transaction
step' cfg txid (InTx s1 (Just s2)) | valid $ getTxCtx txid' cfg = 
  case step' cfg txid' s2 of
    Just (cfg', stmt', l) -> return (cfg', Just $ InTx s1 stmt', "tx/" ++ l)
    Nothing               -> return (rollback txid' cfg, Just $ Atomic s1, "rollback")
                                   | otherwise                  = return (rollback txid' cfg, Just $ Atomic s1, "rollback")
  where txid' = succTx txid

-- ending a transaction
step' cfg txid (InTx s1 Nothing) | valid $ getTxCtx txid' cfg = return (commit txid' cfg, Nothing, "commit")
                                 | otherwise                  = return (rollback txid' cfg, Just $ Atomic s1, "rollback")
  where txid' = succTx txid

commit :: TxID -> ECfg -> ECfg
commit txid cfg = cfg { varOwn = locksToParent txid (varOwn cfg),
                        txCtx = mergeParent txid (txCtx cfg)
                      }

rollback :: TxID -> ECfg -> ECfg
rollback txid cfg = cfg { store = Map.foldWithKey (\k v s -> if hasWrite txid k (varOwn cfg) then Map.insert k v s else s) (store cfg) $ history $ getTxCtx txid cfg,
                          varOwn = dropLocks txid (varOwn cfg),
                          txCtx = Map.delete txid (txCtx cfg)
                        }
