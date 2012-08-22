module Strong where

open import Core
open import Data.Nat
open import Data.Bool

⟦_⟧ : {n : ℕ}{a : Set} → Exp n a → Mem n → a
⟦ V x ⟧      m = lookup x m
⟦ N x ⟧      m = x
⟦ a₁ :+ a₂ ⟧ m = ⟦ a₁ ⟧ m + ⟦ a₂ ⟧ m
⟦ a₁ :- a₂ ⟧ m = ⟦ a₁ ⟧ m ∸ ⟦ a₂ ⟧ m
⟦ a₁ :× a₂ ⟧ m = ⟦ a₁ ⟧ m * ⟦ a₂ ⟧ m
⟦ true ⟧     m = true
⟦ false ⟧    m = false
⟦ ¬ b ⟧      m = not (⟦ b ⟧ m)
⟦ a₁ == a₂ ⟧ m = ⟦ a₁ ⟧ m =ℕ ⟦ a₂ ⟧ m
⟦ a₁ <= a₂ ⟧ m = ⟦ a₁ ⟧ m ≤ℕ ⟦ a₂ ⟧ m
⟦ b₁ :∨ b₂ ⟧ m = ⟦ b₁ ⟧ m ∨ ⟦ b₂ ⟧ m
⟦ b₁ :∧ b₂ ⟧ m = ⟦ b₁ ⟧ m ∧ ⟦ b₂ ⟧ m

data Cfg (n : ℕ) : Set where
   ⟨_/_⟩          : Stmt n → Mem n → Cfg n
   ⟨_⟩            : Mem n → Cfg n 

mutual
 data _⟶_ {n : ℕ} : Cfg n → Cfg n → Set where
  Skip⟶   : {m : Mem n} → 
    ⟨ Skip / m ⟩ ⟶ ⟨ m ⟩
  ,,⟶Fin  : {s0 s1 : Stmt n}{m m' : Mem n} → 
    ⟨ s0 / m ⟩ ⟶ ⟨ m' ⟩ → 
    ⟨ s0 ,, s1 / m ⟩ ⟶ ⟨ s1 / m' ⟩
  ,,⟶Step : {s0 s1 s0' : Stmt n}{m m' : Mem n} → 
    ⟨ s0 / m ⟩ ⟶ ⟨ s0' / m' ⟩ → 
    ⟨ s0 ,, s1 / m ⟩ ⟶ ⟨ s0' ,, s1 / m' ⟩ 
  ∥⟶₁Fin  : {s₁ s₂ : Stmt n}{m m' : Mem n} → 
    ⟨ s₁ / m ⟩ ⟶ ⟨ m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₂ / m' ⟩
  ∥⟶₁Step : {s₁ s₁' s₂ : Stmt n}{m m' : Mem n} → 
    ⟨ s₁ / m ⟩ ⟶ ⟨ s₁' / m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₁' ∥ s₂ / m' ⟩ 
  ∥⟶₂Fin  : {s₁ s₂ : Stmt n}{m m' : Mem n} → 
    ⟨ s₂ / m ⟩ ⟶ ⟨ m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₁ / m' ⟩
  ∥⟶₂Step : {s₁ s₂ s₂' : Stmt n}{m m' : Mem n} → 
    ⟨ s₂ / m ⟩ ⟶ ⟨ s₂' / m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₁ ∥ s₂' / m' ⟩ 
  If⟶ : {s₁ s₂ : Stmt n}{m : Mem n}{b : Exp n Bool} → 
    ⟨ If b then s₁ else s₂ / m ⟩ ⟶
    ⟨ if ⟦ b ⟧ m then s₁ else s₂ / m ⟩
  While⟶True : {s : Stmt n}{b : Exp n Bool}{m : Mem n} →
    T (⟦ b ⟧ m) → 
    ⟨ While b do s / m ⟩ ⟶ ⟨ s ,, While b do s / m ⟩
  While⟶False : {s : Stmt n}{b : Exp n Bool}{m : Mem n} →
    T (not (⟦ b ⟧ m)) → 
    ⟨ While b do s / m ⟩ ⟶ ⟨ m ⟩
  :=⟶ : {x : Var n}{a : Exp n ℕ}{m : Mem n} →
    ⟨ x := a / m ⟩ ⟶ ⟨ m [ x ]≔ ⟦ a ⟧ m ⟩
  Trans⟶ : {s : Stmt n}{m m' : Mem n} → 
    ⟨ s / m ⟩ ⟶* ⟨ m' ⟩ →
    ⟨ Trans s / m ⟩ ⟶ ⟨ m' ⟩

 data _⟶*_ {n : ℕ} : Cfg n → Cfg n → Set where
  Finish : {c : Cfg n} → c ⟶* c
  Step   : {c c' c'' : Cfg n} → 
    c ⟶ c' → c' ⟶* c'' → 
    c ⟶* c''

concat* : {n : ℕ}{c c' c'' : Cfg n} → c ⟶* c' → c' ⟶* c'' → c ⟶* c''
concat* p Finish = p
concat* Finish q = q
concat* (Step p₁ p₂) q = Step p₁ (concat* p₂ q)

lem,,⟶Fin : {n : ℕ} {s s* : Stmt n} {m m' : Mem n} → ⟨ s / m ⟩ ⟶* ⟨ m' ⟩ → ⟨ s ,, s* / m ⟩ ⟶* ⟨ s* / m' ⟩
lem,,⟶Fin (Step p Finish) = Step (,,⟶Fin p) Finish
lem,,⟶Fin (Step Skip⟶ (Step () _))
lem,,⟶Fin (Step (,,⟶Fin p) (Step q r))  = Step (,,⟶Step (,,⟶Fin p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (,,⟶Step p) (Step q r)) = Step (,,⟶Step (,,⟶Step p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (∥⟶₁Fin p) (Step q r)) = Step (,,⟶Step (∥⟶₁Fin p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (∥⟶₁Step p) (Step q r)) = Step (,,⟶Step (∥⟶₁Step p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (∥⟶₂Fin p) (Step q r)) = Step (,,⟶Step (∥⟶₂Fin p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (∥⟶₂Step p) (Step q r)) = Step (,,⟶Step (∥⟶₂Step p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step If⟶ (Step q r)) = Step (,,⟶Step If⟶) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (While⟶True p) (Step q r)) = Step (,,⟶Step (While⟶True p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (While⟶False p) (Step () r)) 
lem,,⟶Fin (Step :=⟶ (Step () r)) 
lem,,⟶Fin (Step (Trans⟶ p) q) =  Step (,,⟶Fin (Trans⟶ (concat* p q))) Finish

lem,,⟶Step : {n : ℕ} {s s' s* : Stmt n} {m m' : Mem n} → ⟨ s / m ⟩ ⟶* ⟨ s' / m' ⟩ → ⟨ s ,, s* / m ⟩ ⟶* ⟨ s' ,, s* / m' ⟩
lem,,⟶Step Finish = Finish
lem,,⟶Step (Step p Finish) = Step (,,⟶Step p) Finish
lem,,⟶Step (Step Skip⟶ (Step () _))
lem,,⟶Step (Step (,,⟶Fin p) (Step q r))  = Step (,,⟶Step (,,⟶Fin p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (,,⟶Step p) (Step q r)) = Step (,,⟶Step (,,⟶Step p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (∥⟶₁Fin p) (Step q r)) = Step (,,⟶Step (∥⟶₁Fin p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (∥⟶₁Step p) (Step q r)) = Step (,,⟶Step (∥⟶₁Step p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (∥⟶₂Fin p) (Step q r)) = Step (,,⟶Step (∥⟶₂Fin p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (∥⟶₂Step p) (Step q r)) = Step (,,⟶Step (∥⟶₂Step p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step If⟶ (Step q r)) = Step (,,⟶Step If⟶) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (While⟶True p) (Step q r)) = Step (,,⟶Step (While⟶True p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (While⟶False p) (Step () r)) 
lem,,⟶Step (Step :=⟶ (Step () r)) 
lem,,⟶Step (Step (Trans⟶ _) (Step () _))

lem∥⟶₁Fin : {n : ℕ} {s s* : Stmt n} {m m' : Mem n} → ⟨ s / m ⟩ ⟶* ⟨ m' ⟩ → ⟨ s ∥ s* / m ⟩ ⟶* ⟨ s* / m' ⟩
lem∥⟶₁Fin (Step p Finish) = Step (∥⟶₁Fin p) Finish
lem∥⟶₁Fin (Step Skip⟶ (Step () _))
lem∥⟶₁Fin (Step (,,⟶Fin p) (Step q r))  = Step (∥⟶₁Step (,,⟶Fin p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (,,⟶Step p) (Step q r)) = Step (∥⟶₁Step (,,⟶Step p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₁Fin p) (Step q r)) = Step (∥⟶₁Step (∥⟶₁Fin p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₁Step p) (Step q r)) = Step (∥⟶₁Step (∥⟶₁Step p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₂Fin p) (Step q r)) = Step (∥⟶₁Step (∥⟶₂Fin p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₂Step p) (Step q r)) = Step (∥⟶₁Step (∥⟶₂Step p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step If⟶ (Step q r)) = Step (∥⟶₁Step If⟶) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (While⟶True p) (Step q r)) = Step (∥⟶₁Step (While⟶True p)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (While⟶False p) (Step () r)) 
lem∥⟶₁Fin (Step :=⟶ (Step () r)) 
lem∥⟶₁Fin (Step (Trans⟶ p) q) =  Step (∥⟶₁Fin (Trans⟶ (concat* p q))) Finish

lem∥⟶₁Step : {n : ℕ} {s s' s* : Stmt n} {m m' : Mem n} → ⟨ s / m ⟩ ⟶* ⟨ s' / m' ⟩ → ⟨ s ∥ s* / m ⟩ ⟶* ⟨ s' ∥ s* / m' ⟩
lem∥⟶₁Step Finish = Finish
lem∥⟶₁Step (Step p Finish) = Step (∥⟶₁Step p) Finish
lem∥⟶₁Step (Step Skip⟶ (Step () _))
lem∥⟶₁Step (Step (,,⟶Fin p) (Step q r))  = Step (∥⟶₁Step (,,⟶Fin p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (,,⟶Step p) (Step q r)) = Step (∥⟶₁Step (,,⟶Step p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₁Fin p) (Step q r)) = Step (∥⟶₁Step (∥⟶₁Fin p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₁Step p) (Step q r)) = Step (∥⟶₁Step (∥⟶₁Step p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₂Fin p) (Step q r)) = Step (∥⟶₁Step (∥⟶₂Fin p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₂Step p) (Step q r)) = Step (∥⟶₁Step (∥⟶₂Step p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step If⟶ (Step q r)) = Step (∥⟶₁Step If⟶) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (While⟶True p) (Step q r)) = Step (∥⟶₁Step (While⟶True p)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (While⟶False p) (Step () r)) 
lem∥⟶₁Step (Step :=⟶ (Step () r)) 
lem∥⟶₁Step (Step (Trans⟶ _) (Step () _))

lem∥⟶₂Fin : {n : ℕ} {s s* : Stmt n} {m m' : Mem n} → ⟨ s / m ⟩ ⟶* ⟨ m' ⟩ → ⟨ s* ∥ s / m ⟩ ⟶* ⟨ s* / m' ⟩
lem∥⟶₂Fin (Step p Finish) = Step (∥⟶₂Fin p) Finish
lem∥⟶₂Fin (Step Skip⟶ (Step () _))
lem∥⟶₂Fin (Step (,,⟶Fin p) (Step q r))  = Step (∥⟶₂Step (,,⟶Fin p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (,,⟶Step p) (Step q r)) = Step (∥⟶₂Step (,,⟶Step p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₁Fin p) (Step q r)) = Step (∥⟶₂Step (∥⟶₁Fin p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₁Step p) (Step q r)) = Step (∥⟶₂Step (∥⟶₁Step p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₂Fin p) (Step q r)) = Step (∥⟶₂Step (∥⟶₂Fin p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₂Step p) (Step q r)) = Step (∥⟶₂Step (∥⟶₂Step p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step If⟶ (Step q r)) = Step (∥⟶₂Step If⟶) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (While⟶True p) (Step q r)) = Step (∥⟶₂Step (While⟶True p)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (While⟶False p) (Step () r)) 
lem∥⟶₂Fin (Step :=⟶ (Step () r)) 
lem∥⟶₂Fin (Step (Trans⟶ p) q) =  Step (∥⟶₂Fin (Trans⟶ (concat* p q))) Finish

lem∥⟶₂Step : {n : ℕ} {s s' s* : Stmt n} {m m' : Mem n} → ⟨ s / m ⟩ ⟶* ⟨ s' / m' ⟩ → ⟨ s* ∥ s / m ⟩ ⟶* ⟨ s* ∥ s' / m' ⟩
lem∥⟶₂Step Finish = Finish
lem∥⟶₂Step (Step p Finish) = Step (∥⟶₂Step p) Finish
lem∥⟶₂Step (Step Skip⟶ (Step () _))
lem∥⟶₂Step (Step (,,⟶Fin p) (Step q r))  = Step (∥⟶₂Step (,,⟶Fin p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (,,⟶Step p) (Step q r)) = Step (∥⟶₂Step (,,⟶Step p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₁Fin p) (Step q r)) = Step (∥⟶₂Step (∥⟶₁Fin p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₁Step p) (Step q r)) = Step (∥⟶₂Step (∥⟶₁Step p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₂Fin p) (Step q r)) = Step (∥⟶₂Step (∥⟶₂Fin p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₂Step p) (Step q r)) = Step (∥⟶₂Step (∥⟶₂Step p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step If⟶ (Step q r)) = Step (∥⟶₂Step If⟶) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (While⟶True p) (Step q r)) = Step (∥⟶₂Step (While⟶True p)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (While⟶False p) (Step () r)) 
lem∥⟶₂Step (Step :=⟶ (Step () r)) 
lem∥⟶₂Step (Step (Trans⟶ _) (Step () _))
