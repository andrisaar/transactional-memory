
module Language where
import Data.Map (Map)
import Data.Maybe (isJust)

type Var = String

data AExp =
  AExp :+ AExp | AExp :- AExp | AExp :* AExp | V Var | N Integer
  deriving (Show, Eq)

data BExp =
  AExp :== AExp | AExp :<= AExp | Not BExp | BExp :&& BExp | BExp :|| BExp | TT | FF
  deriving (Show, Eq)

data Stmt =
  Skip |
  Stmt :\ Stmt |
  Var := AExp |
  If BExp Stmt Stmt |
  While BExp Stmt |
  Atomic Stmt |
  Spawn [Stmt] |
  InTx Stmt (Maybe Stmt)
  deriving (Show, Eq)

--

type Store = Map Var Integer

type ThreadStore = [Maybe Stmt]

type ThreadID = Integer

singleThreadStore :: Stmt -> ThreadStore
singleThreadStore stmt = [Just stmt]

availableThreads :: ThreadStore -> [Integer]
availableThreads ts = map snd $ filter (isJust . fst) $ zip ts [0..]

(!!?)                    :: [a] -> Integer -> Maybe a
xs     !!? n | n < 0 =  Nothing
[]     !!? _         =  Nothing
(x:_)  !!? 0         =  Just x
(_:xs) !!? n         =  xs !!? (n-1)

updt :: Integer -> Maybe Stmt -> ThreadStore -> ThreadStore
updt 0 s (_:ts) = s : ts
updt n s (t:ts) = t : (updt (n-1) s ts)

append :: Stmt -> ThreadStore -> ThreadStore
append stmt ts = ts ++ [Just stmt]

