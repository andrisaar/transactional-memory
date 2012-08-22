module Core where

open import Data.Nat
open import Data.Bool
open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; _[_]≔_; lookup)

_=ℕ_ : ℕ → ℕ → Bool
zero  =ℕ zero  = true
zero  =ℕ suc _ = false
suc _ =ℕ zero  = false
suc n =ℕ suc m = n =ℕ m

_≤ℕ_ : ℕ → ℕ → Bool
zero  ≤ℕ _     = true
suc _ ≤ℕ zero  = false
suc n ≤ℕ suc m = n ≤ℕ m

Var : (n : ℕ) → Set
Var n = Fin n

Mem : (n : ℕ) → Set
Mem n = Vec ℕ n

data Exp (n : ℕ) : Set → Set where
  V     : Var n → Exp n ℕ
  N     : ℕ → Exp n ℕ
  _:+_  : Exp n ℕ → Exp n ℕ → Exp n ℕ
  _:-_  : Exp n ℕ → Exp n ℕ → Exp n ℕ
  _:×_  : Exp n ℕ → Exp n ℕ → Exp n ℕ 
  true  : Exp n Bool
  false : Exp n Bool
  ¬     : Exp n Bool → Exp n Bool
  _==_  : Exp n ℕ → Exp n ℕ → Exp n Bool
  _<=_  : Exp n ℕ → Exp n ℕ → Exp n Bool
  _:∨_  : Exp n Bool → Exp n Bool → Exp n Bool
  _:∧_  : Exp n Bool → Exp n Bool → Exp n Bool

data Stmt (n : ℕ) : Set where
  _:=_          : Var n → Exp n ℕ → Stmt n
  If_then_else_ : Exp n Bool → Stmt n → Stmt n → Stmt n
  While_do_     : Exp n Bool → Stmt n → Stmt n
  Skip          : Stmt n
  Trans_        : Stmt n → Stmt n
  _,,_          : Stmt n → Stmt n → Stmt n
  _∥_          : Stmt n → Stmt n → Stmt n