module Lazy where

open import Core
open import Data.Bool
open import Data.Nat
open import Data.Vec public using (_∷_; [])
open import Data.Maybe.Core
open import Data.Product
open import Function

open import Relation.Binary.PropositionalEquality

Height : Set
Height = ℕ

Cache : (n : ℕ) → Set
Cache n = Vec (Maybe ℕ) n

data Stack (n : ℕ) : (h : Height) → Set where
  _◁     : Mem n → Stack n 0
  _≪_≪_ : {h : Height} → Cache n → Cache n → Stack n h → Stack n (suc h) 

peel : {n s : ℕ} → Stack (suc n) s → Stack n s
peel ((_ ∷ m) ◁) = m ◁
peel ((_ ∷ wc) ≪ (_ ∷ rc) ≪ mw) = wc ≪ rc ≪ peel mw

read : {n s : ℕ} → Var n → Stack n s → ℕ
read x (m ◁) = lookup x m

read zero ((mbrv ∷ _) ≪ (mbwv ∷ _) ≪ mw) = f mbrv mbwv (read zero mw)
  where
  f : Maybe ℕ → Maybe ℕ → ℕ →  ℕ
  f (just v)  _       _ = v
  f nothing  (just v) _ = v
  f nothing  nothing  v = v 

read (suc x) ((_ ∷ wc) ≪ (_ ∷ rc) ≪ m) = read x (wc ≪ rc ≪ peel m)

_≈_ : {n h h' : ℕ} → Stack n h → Stack n h' → Set
xm₁ ≈ xm₂ = (x : Var _) → read x xm₁ ≡ read x xm₂

{-
_≈_ : {n h : ℕ} → Stack n h → Mem n → Set
xm ≈ m = (x : Var _) → read x xm ≡ lookup x m
-}

_≺_ : {n h : ℕ} → Cache n → Stack n h → Set
c ≺ xm = (x : Var _) {v : ℕ} → lookup x c ≡ just v → v ≡ read x xm

merge : {n : ℕ} → Cache n → Mem n → Mem n
merge []            []      = []
merge (u ∷ c)       (v ∷ m)  = f u v ∷ merge c m
  where
  f : Maybe ℕ → ℕ → ℕ
  f nothing  v = v
  f (just v) _ = v

wcmerge : {n : ℕ} → Cache n → Cache n → Cache n
wcmerge []            []         = []
wcmerge (u ∷ c)       (v ∷ wc)   = f u v ∷ wcmerge c wc
  where
  f : Maybe ℕ → Maybe ℕ → Maybe ℕ
  f nothing v = v
  f v       _ = v

rcmerge : {n : ℕ} → Cache n → Cache n → Cache n → Cache n
rcmerge []            _             []             = []
rcmerge (t ∷ c)       (u ∷ wc)      (v  ∷ rc)      = f t u v ∷ rcmerge c wc rc
  where
  f : Maybe ℕ → Maybe ℕ → Maybe ℕ → Maybe ℕ
  f (just v) nothing nothing  = just v
  f _        _       v        = v

write : {n s : ℕ} → Cache n → Stack n s → Stack n s
write c (m ◁)           = merge c m ◁ 
write c (wc ≪ rc ≪ mw) = wcmerge c wc ≪ rc ≪ mw

rcupdate : {n s : ℕ} → Cache n → Stack n s → Stack n s
rcupdate c (m ◁)          = m ◁
rcupdate c (wc ≪ rc ≪ mw) = wc ≪ rcmerge c wc rc ≪ mw

∅ : {n : ℕ} → Cache n
∅ {zero}  = []
∅ {suc _} = nothing ∷ ∅

⟦_⟧₂ : {n s : ℕ}{A : Set} → Exp n A → Stack n s → Stack n s
⟦ V x ⟧₂      xm = rcupdate (∅ [ x ]≔ just (read x xm)) xm
⟦ N _ ⟧₂      xm = xm
⟦ a₁ :+ a₂ ⟧₂ xm = ⟦ a₂ ⟧₂ (⟦ a₁ ⟧₂ xm)
⟦ a₁ :- a₂ ⟧₂ xm = ⟦ a₂ ⟧₂ (⟦ a₁ ⟧₂ xm)
⟦ a₁ :× a₂ ⟧₂ xm = ⟦ a₂ ⟧₂ (⟦ a₁ ⟧₂ xm)
⟦ true ⟧₂     xm = xm
⟦ false ⟧₂    xm = xm
⟦ ¬ b ⟧₂      xm = ⟦ b ⟧₂ xm
⟦ a₁ == a₂ ⟧₂ xm = ⟦ a₂ ⟧₂ (⟦ a₁ ⟧₂ xm)
⟦ a₁ <= a₂ ⟧₂ xm = ⟦ a₂ ⟧₂ (⟦ a₁ ⟧₂ xm)
⟦ b₁ :∨ b₂ ⟧₂ xm = ⟦ b₂ ⟧₂ (⟦ b₁ ⟧₂ xm)
⟦ b₁ :∧ b₂ ⟧₂ xm = ⟦ b₂ ⟧₂ (⟦ b₁ ⟧₂ xm)

⟦_⟧₁ : {n s : ℕ}{A : Set} → Exp n A → Stack n s → A
⟦ V x ⟧₁      xm = read x xm
⟦ N n ⟧₁      _  = n
⟦ a₁ :+ a₂ ⟧₁ xm = (⟦ a₁ ⟧₁ xm) + (⟦ a₂ ⟧₁ (⟦ a₁ ⟧₂ xm))
⟦ a₁ :- a₂ ⟧₁ xm = (⟦ a₁ ⟧₁ xm) ∸ (⟦ a₂ ⟧₁ (⟦ a₁ ⟧₂ xm))
⟦ a₁ :× a₂ ⟧₁ xm = (⟦ a₁ ⟧₁ xm) * (⟦ a₂ ⟧₁ (⟦ a₁ ⟧₂ xm))
⟦ true ⟧₁     _  = true
⟦ false ⟧₁    _  = false
⟦ ¬ b ⟧₁      xm = not (⟦ b ⟧₁ xm)
⟦ a₁ == a₂ ⟧₁ xm = (⟦ a₁ ⟧₁ xm) =ℕ (⟦ a₂ ⟧₁ (⟦ a₁ ⟧₂ xm))
⟦ a₁ <= a₂ ⟧₁ xm = (⟦ a₁ ⟧₁ xm) ≤ℕ (⟦ a₂ ⟧₁ (⟦ a₁ ⟧₂ xm))
⟦ b₁ :∨ b₂ ⟧₁ xm = (⟦ b₁ ⟧₁ xm) ∨ (⟦ b₂ ⟧₁ (⟦ b₁ ⟧₂ xm))
⟦ b₁ :∧ b₂ ⟧₁ xm = (⟦ b₁ ⟧₁ xm) ∧ (⟦ b₂ ⟧₁ (⟦ b₁ ⟧₂ xm))

⟦_⟧ : {n s : ℕ}{A : Set} → Exp n A → Stack n s → (A × Stack n s)
⟦ e ⟧ xm = ⟦ e ⟧₁ xm , ⟦ e ⟧₂ xm

data XStmt (n : ℕ) : Set where
  _:=_          : Var n → Exp n ℕ → XStmt n
  If_then_else_ : Exp n Bool → Stmt n → Stmt n → XStmt n
  While_do_     : Exp n Bool → Stmt n → XStmt n
  Skip          : XStmt n
  Trans_        : Stmt n → XStmt n
  _,,_          : XStmt n → Stmt n → XStmt n
  _∥_          : XStmt n → XStmt n → XStmt n
  Intrans       : XStmt n → Stmt n → Cache n → Cache n → XStmt n
  Trycommit     : Stmt n → Cache n → Cache n → XStmt n

emb : {n : ℕ} → Stmt n → XStmt n
emb (x := a) = x := a
emb (If b then s else s') = If b then s else s'
emb (While b do s) = While b do s
emb Skip = Skip
emb (Trans s) = Trans s
emb (s₁ ,, s₂) = emb s₁ ,, s₂
emb (s₁ ∥ s₂) = emb s₁ ∥ emb s₂

data Cfg (n s : ℕ) : Set where
   ⟨_/_⟩          : XStmt n → Stack n s → Cfg n s
   ⟨_⟩            : Stack n s → Cfg n s

mutual
 data _⟶_ {n h : ℕ} : Cfg n h → Cfg n h → Set where
  Skip⟶   : {m : Stack n h} → 
    ⟨ Skip / m ⟩ ⟶ ⟨ m ⟩
  ,,⟶Fin  : {s0 : XStmt n}{s1 : Stmt n}{m m' : Stack n h} → 
    ⟨ s0 / m ⟩ ⟶ ⟨ m' ⟩ → 
    ⟨ s0 ,, s1 / m ⟩ ⟶ ⟨ emb s1 / m' ⟩
  ,,⟶Step : {s0 s0' : XStmt n} {s1 : Stmt n}{m m' : Stack n h} → 
    ⟨ s0 / m ⟩ ⟶ ⟨ s0' / m' ⟩ → 
    ⟨ s0 ,, s1 / m ⟩ ⟶ ⟨ s0' ,, s1 / m' ⟩ 
  ∥⟶₁Fin : {s₁ s₂ : XStmt n}{m m' : Stack n h} → 
    ⟨ s₁ / m ⟩ ⟶ ⟨ m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₂ / m' ⟩
  ∥⟶₁Step : {s₁ s₁' s₂ : XStmt n}{m m' : Stack n h} → 
    ⟨ s₁ / m ⟩ ⟶ ⟨ s₁' / m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₁' ∥ s₂ / m' ⟩ 
  ∥⟶₂Fin : {s₁ s₂ : XStmt n}{m m' : Stack n h} → 
    ⟨ s₂ / m ⟩ ⟶ ⟨ m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₁ / m' ⟩
  ∥⟶₂Step : {s₁ s₂ s₂' : XStmt n}{m m' : Stack n h} → 
    ⟨ s₂ / m ⟩ ⟶ ⟨ s₂' / m' ⟩ → 
    ⟨ s₁ ∥ s₂ / m ⟩ ⟶ ⟨ s₁ ∥ s₂' / m' ⟩ 
  If⟶ : {s₁ s₂ : Stmt n}{xm : Stack n h}{b : Exp n Bool} → 
    ⟨ If b then s₁ else s₂ / xm ⟩ ⟶ ⟨ emb (if ⟦ b ⟧₁ xm then s₁ else s₂) / ⟦ b ⟧₂ xm ⟩
  While⟶True : {s : Stmt n}{b : Exp n Bool}{m : Stack n h} → 
    T (⟦ b ⟧₁ m) →
    ⟨ While b do s / m ⟩ ⟶ ⟨ emb s ,, While b do s / ⟦ b ⟧₂ m ⟩
  While⟶False : {s : Stmt n}{b : Exp n Bool}{m : Stack n h} → 
    T (not (⟦ b ⟧₁ m)) →
    ⟨ While b do s / m ⟩ ⟶ ⟨ ⟦ b ⟧₂ m ⟩
  :=⟶ : {x : Var n}{a : Exp n ℕ}{m : Stack n h} →
    ⟨ x := a / m ⟩ ⟶ ⟨ write (∅ [ x ]≔ just (⟦ a ⟧₁ m)) (⟦ a ⟧₂ m) ⟩
  Trans⟶ : {s : Stmt n}{m : Stack n h} → 
    ⟨ Trans s / m ⟩ ⟶ ⟨ Intrans (emb s) s ∅ ∅ / m ⟩ 
  Intrans⟶Step : {xs xs' : XStmt n}{s : Stmt n}{wc rc wc' rc' : Cache n}{m : Stack n h} →
    ⟨ xs / wc ≪ rc ≪ m ⟩ ⟶ ⟨ xs' / wc' ≪ rc' ≪ m ⟩ → 
    ⟨ Intrans xs s wc rc / m ⟩ ⟶ ⟨ Intrans xs' s wc' rc' / m ⟩
  Intrans⟶Fin : {xs : XStmt n}{s : Stmt n}{wc rc wc' rc' : Cache n}{m : Stack n h} → 
    ⟨ xs / wc ≪ rc ≪ m ⟩ ⟶ ⟨ wc' ≪ rc' ≪ m ⟩ → 
    ⟨ Intrans xs s wc rc / m ⟩ ⟶ ⟨ Trycommit s wc' rc' / m ⟩
  Commit : {s : Stmt n} {wc rc : Cache n} 
    (m : Stack n h) → rc ≺ m → 
    ⟨ Trycommit s wc rc / m ⟩ ⟶ ⟨ write wc (rcupdate rc m) ⟩
  Abort : {s : Stmt n}{wc rc : Cache n}{m : Stack n h} → 
    ⟨ Trycommit s wc rc / m ⟩ ⟶ ⟨ Trans s / m ⟩
  Giveup : {xs : XStmt n}{s : Stmt n}{wc rc : Cache n}{m : Stack n h} → 
    ⟨ Intrans xs s wc rc / m ⟩ ⟶ ⟨ Trans s / m ⟩

 data _⟶*_ {n h : ℕ} : Cfg n h → Cfg n h → Set where
  Finish : {c : Cfg n h} → c ⟶* c
  Step   : {c c' c'' : Cfg n h} → 
    c ⟶ c' → c' ⟶* c'' → 
    c ⟶* c''

--
-- Properties
--

lemmapeel : {n s : ℕ} → (mw : Stack (suc n) s) → (x : Var n) → read x (peel mw) ≡ read (suc x) mw
lemmapeel ((_ ∷ _) ◁) _ = refl
lemmapeel ((_ ∷ _) ≪ (_ ∷ _) ≪ _) _ = refl

-- 1. Empty cache is always consistent with all stacks
consempty : {n h : ℕ} → (xm : Stack n h) → ∅ ≺ xm
consempty _ zero ()
consempty ((_ ∷ m) ◁)                (suc x) p = consempty (m ◁) x p
consempty ((_ ∷ wc) ≪ (_ ∷ rc) ≪ xm) (suc x) p = consempty (wc ≪ rc ≪ peel xm) x p

-- 2. Given a cache c that is consistent with stack xm, if we update that cache
--    with some value read from that stack, then the resulting cache is also
--    consistent with stack xm.
consupdate : {n h : ℕ}{x : Var n} (c : Cache n) (xm : Stack n h) → c ≺ xm → (c [ x ]≔ just (read x xm)) ≺ xm
consupdate {zero}  {_}     {()}    _       _               _ _       _
consupdate {suc n} {zero}  {zero}  (_ ∷ _) ((_ ∷ _) ◁)     p zero    refl = refl
consupdate {suc n} {zero}  {zero}  (_ ∷ c) ((_ ∷ m) ◁)     p (suc y) q    = p (suc y) q
consupdate {suc n} {zero}  {suc x} (_ ∷ _) ((_ ∷ _) ◁)     p zero    q    = p zero q
consupdate {suc n} {zero}  {suc x} (_ ∷ c) ((_ ∷ m) ◁)     p (suc y) q    = consupdate {n} {zero} {x} c (m ◁) (p ∘ suc) y q
consupdate {suc n} {suc h} {zero}  (_ ∷ _) (wc ≪ rc ≪ xm) p zero    refl = refl
consupdate {suc n} {suc h} {zero}  (_ ∷ _) (wc ≪ rc ≪ xm) p (suc y) q    = p (suc y) q
consupdate {suc n} {suc h} {suc x} (_ ∷ c) ((_ ∷ wc) ≪ (_ ∷ rc) ≪ xm) p zero q = p zero q
consupdate {suc n} {suc h} {suc x} (_ ∷ c) ((_ ∷ wc) ≪ (_ ∷ rc) ≪ xm) p (suc y) q = consupdate {n} {suc h} c (wc ≪ rc ≪ peel xm) (p ∘ suc) y q

Lemma1 : ∀{n h h'} → (xm₁ : Stack n h) → (xm₂ : Stack n h') → (rc : Cache n) → xm₁ ≈ xm₂ → rc ≺ xm₁ → rcupdate rc xm₁ ≈ xm₂
Lemma1 (_ ◁)                                   _   _            p _ x    = p x
Lemma1 xm₁                                     _   [] _ _ ()
Lemma1 ((just _  ∷ _)   ≪ _       ∷ _   ≪ _)   _   (just _ ∷ _)   p _ zero = p zero
Lemma1 ((nothing ∷ _)   ≪ just _  ∷ _   ≪ _)   _   (just _ ∷ _)   p _ zero = p zero
Lemma1 ((nothing ∷ _)   ≪ nothing ∷ _   ≪ _)   _   (just _ ∷ _)   p q zero rewrite sym (p zero) = q zero refl
Lemma1 ((just _  ∷ _)   ≪ _       ∷ _   ≪ _)   _   (nothing ∷ rc) p _ zero = p zero
Lemma1 ((nothing ∷ _)   ≪ just _  ∷ _   ≪ _)   _   (nothing ∷ rc) p _ zero = p zero
Lemma1 ((nothing ∷ _)   ≪ nothing ∷ _   ≪ _)   _   (nothing ∷ rc) p _ zero = p zero
Lemma1 ((_       ∷ wc') ≪ _       ∷ rc' ≪ xm₁) ((_ ∷ wc₂) ◁)               (_ ∷ rc) p q (suc x) = 
    Lemma1 (wc' ≪ rc' ≪ peel xm₁) (wc₂ ◁) rc (p ∘ suc) (q ∘ suc) x
Lemma1 ((_       ∷ wc') ≪ _       ∷ rc' ≪ xm₁) ((_ ∷ wc₂) ≪ _ ∷ rc₂ ≪ xm₂) (_ ∷ rc) p q (suc x) =
    Lemma1 (wc' ≪ rc' ≪ peel xm₁) (wc₂ ≪ rc₂ ≪ peel xm₂) rc (p ∘ suc) (q ∘ suc) x

{-
-- 3. If a read cache is consistent with a stack, then for the purpose of reading it
--    doesn't matter if we merge the cache into the stack or not.
rcmerge≡ : {n h : ℕ} (rc : Cache n) (xm : Stack n h) → rc ≺ xm → (x : Var n) → read x (rcupdate rc xm) ≡ read x xm
rcmerge≡ _              (_ ◁)                                _ _       = refl
rcmerge≡ []             ([]            ≪ []            ≪ _)  _ _       = refl
rcmerge≡ (just _ ∷ rc)  ((just _ ∷ _)  ≪ (_ ∷ _)       ≪ _)  _ zero    = refl
rcmerge≡ (just _ ∷ rc)  ((nothing ∷ _) ≪ (just _ ∷ _)  ≪ _)  _ zero    = refl
rcmerge≡ (just _ ∷ rc)  ((nothing ∷ _) ≪ (nothing ∷ _) ≪ _)  p zero    = p zero refl
rcmerge≡ (nothing ∷ rc) ((just _ ∷ _)  ≪ (_ ∷ _)       ≪ _)  _ zero    = refl
rcmerge≡ (nothing ∷ rc) ((nothing ∷ _) ≪ (just _ ∷ _)  ≪ _)  _ zero    = refl
rcmerge≡ (nothing ∷ rc) ((nothing ∷ _) ≪ (nothing ∷ _) ≪ _)  _ zero    = refl
rcmerge≡ (_ ∷ rc)       ((_ ∷ wc')     ≪ (_ ∷ rc')     ≪ xm) p (suc x) = rcmerge≡ rc (wc' ≪ rc' ≪ peel xm) (λ x → p (suc x)) x
-}
merge≡ : {n : ℕ} → (m : Mem n) → merge ∅ m ≡ m
merge≡ [] = refl
merge≡ (_ ∷ m) rewrite merge≡ m = refl

wcmerge≡ : {n : ℕ} → (c : Cache n) → wcmerge ∅ c ≡ c
wcmerge≡ [] = refl
wcmerge≡ (_ ∷ m) rewrite wcmerge≡ m = refl

lem∥⟶₁Fin : {n h : ℕ} {xs₁ xs₂ : XStmt n} {xm xm' : Stack n h} → ⟨ xs₁ / xm ⟩ ⟶* ⟨ xm' ⟩ → ⟨ xs₁ ∥ xs₂ / xm ⟩ ⟶* ⟨ xs₂ / xm' ⟩
lem∥⟶₁Fin (Step p Finish) = Step (∥⟶₁Fin p) Finish
lem∥⟶₁Fin (Step Skip⟶ (Step () r)) 
lem∥⟶₁Fin (Step (,,⟶Fin y) (Step q r)) = Step (∥⟶₁Step (,,⟶Fin y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (,,⟶Step y) (Step q r)) =  Step (∥⟶₁Step (,,⟶Step y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₁Fin y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₁Fin y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₁Step y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₁Step y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₂Fin y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₂Fin y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (∥⟶₂Step y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₂Step y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (If⟶) (Step q r)) =  Step (∥⟶₁Step (If⟶)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (While⟶True y) (Step q r)) =  Step (∥⟶₁Step (While⟶True y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (While⟶False y) (Step () r))
lem∥⟶₁Fin (Step :=⟶ (Step () r)) 
lem∥⟶₁Fin (Step Trans⟶ (Step q r)) =  Step (∥⟶₁Step Trans⟶) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (Intrans⟶Step {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₁Step (Intrans⟶Step  {_} {_} {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (Intrans⟶Fin {xs} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₁Step (Intrans⟶Fin {_} {_} {xs} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step (Commit y _) (Step () r)) 
lem∥⟶₁Fin (Step Abort (Step q r)) = Step (∥⟶₁Step Abort) (lem∥⟶₁Fin (Step q r))
lem∥⟶₁Fin (Step Giveup (Step q r)) = Step (∥⟶₁Step Giveup) (lem∥⟶₁Fin (Step q r))

lem∥⟶₁Step : {n h : ℕ} {xs₁ xs₁' xs₂ : XStmt n} {xm xm' : Stack n h} → ⟨ xs₁ / xm ⟩ ⟶* ⟨ xs₁' / xm' ⟩ → ⟨ xs₁ ∥ xs₂ / xm ⟩ ⟶* ⟨ xs₁' ∥ xs₂ / xm' ⟩
lem∥⟶₁Step Finish = Finish
lem∥⟶₁Step (Step p Finish) = Step (∥⟶₁Step p) Finish
lem∥⟶₁Step (Step Skip⟶ (Step () r)) 
lem∥⟶₁Step (Step (,,⟶Fin y) (Step q r)) = Step (∥⟶₁Step (,,⟶Fin y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (,,⟶Step y) (Step q r)) =  Step (∥⟶₁Step (,,⟶Step y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₁Fin y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₁Fin y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₁Step y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₁Step y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₂Fin y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₂Fin y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (∥⟶₂Step y) (Step q r)) =  Step (∥⟶₁Step (∥⟶₂Step y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step If⟶ (Step q r)) =  Step (∥⟶₁Step If⟶) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (While⟶True y) (Step q r)) =  Step (∥⟶₁Step (While⟶True y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (While⟶False y) (Step () r))
lem∥⟶₁Step (Step :=⟶ (Step () r)) 
lem∥⟶₁Step (Step Trans⟶ (Step q r)) =  Step (∥⟶₁Step Trans⟶) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (Intrans⟶Step {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₁Step (Intrans⟶Step {_} {_} {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (Intrans⟶Fin {xs} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₁Step (Intrans⟶Fin {_} {_} {xs} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step (Commit _ _) (Step () r)) 
lem∥⟶₁Step (Step Abort (Step q r)) = Step (∥⟶₁Step Abort) (lem∥⟶₁Step (Step q r))
lem∥⟶₁Step (Step Giveup (Step q r)) = Step (∥⟶₁Step Giveup) (lem∥⟶₁Step (Step q r))

lem∥⟶₂Fin : {n h : ℕ} {xs₁ xs₂ : XStmt n} {xm xm' : Stack n h} → ⟨ xs₂ / xm ⟩ ⟶* ⟨ xm' ⟩ → ⟨ xs₁ ∥ xs₂ / xm ⟩ ⟶* ⟨ xs₁ / xm' ⟩
lem∥⟶₂Fin (Step p Finish) = Step (∥⟶₂Fin p) Finish
lem∥⟶₂Fin (Step Skip⟶ (Step () r)) 
lem∥⟶₂Fin (Step (,,⟶Fin y) (Step q r)) = Step (∥⟶₂Step (,,⟶Fin y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (,,⟶Step y) (Step q r)) =  Step (∥⟶₂Step (,,⟶Step y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₁Fin y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₁Fin y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₁Step y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₁Step y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₂Fin y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₂Fin y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (∥⟶₂Step y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₂Step y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step If⟶ (Step q r)) =  Step (∥⟶₂Step If⟶) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (While⟶True y) (Step q r)) =  Step (∥⟶₂Step (While⟶True y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (While⟶False y) (Step () r))
lem∥⟶₂Fin (Step :=⟶ (Step () r)) 
lem∥⟶₂Fin (Step Trans⟶ (Step q r)) =  Step (∥⟶₂Step Trans⟶) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (Intrans⟶Step {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₂Step (Intrans⟶Step {_} {_} {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (Intrans⟶Fin {xs} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₂Step (Intrans⟶Fin {_} {_} {xs} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step (Commit _ _) (Step () r)) 
lem∥⟶₂Fin (Step Abort (Step q r)) = Step (∥⟶₂Step Abort) (lem∥⟶₂Fin (Step q r))
lem∥⟶₂Fin (Step Giveup (Step q r)) = Step (∥⟶₂Step Giveup) (lem∥⟶₂Fin (Step q r))

lem∥⟶₂Step : {n h : ℕ} {xs₁ xs₂ xs₂' : XStmt n} {xm xm' : Stack n h} → ⟨ xs₂ / xm ⟩ ⟶* ⟨ xs₂' / xm' ⟩ → ⟨ xs₁ ∥ xs₂ / xm ⟩ ⟶* ⟨ xs₁ ∥ xs₂' / xm' ⟩
lem∥⟶₂Step Finish = Finish
lem∥⟶₂Step (Step p Finish) = Step (∥⟶₂Step p) Finish
lem∥⟶₂Step (Step Skip⟶ (Step () r)) 
lem∥⟶₂Step (Step (,,⟶Fin y) (Step q r)) = Step (∥⟶₂Step (,,⟶Fin y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (,,⟶Step y) (Step q r)) =  Step (∥⟶₂Step (,,⟶Step y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₁Fin y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₁Fin y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₁Step y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₁Step y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₂Fin y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₂Fin y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (∥⟶₂Step y) (Step q r)) =  Step (∥⟶₂Step (∥⟶₂Step y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step If⟶ (Step q r)) =  Step (∥⟶₂Step If⟶) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (While⟶True y) (Step q r)) =  Step (∥⟶₂Step (While⟶True y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (While⟶False y) (Step () r))
lem∥⟶₂Step (Step :=⟶ (Step () r)) 
lem∥⟶₂Step (Step Trans⟶ (Step q r)) =  Step (∥⟶₂Step Trans⟶) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (Intrans⟶Step {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₂Step (Intrans⟶Step {_} {_} {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (Intrans⟶Fin {xs} {s} {wc} {rc} {wc'} {rc'} {m} y) (Step q r)) =  Step (∥⟶₂Step (Intrans⟶Fin {_} {_} {xs} {s} {wc} {rc} {wc'} {rc'} {m} y)) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step (Commit y _) (Step () r)) 
lem∥⟶₂Step (Step Abort (Step q r)) = Step (∥⟶₂Step Abort) (lem∥⟶₂Step (Step q r))
lem∥⟶₂Step (Step Giveup (Step q r)) = Step (∥⟶₂Step Giveup) (lem∥⟶₂Step (Step q r))

lem,,⟶Fin : {n h : ℕ} {xs : XStmt n} {xm xm' : Stack n h} {s : Stmt n} → ⟨ xs / xm ⟩ ⟶* ⟨ xm' ⟩ → ⟨ xs ,, s / xm ⟩ ⟶* ⟨ (emb s) / xm' ⟩
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
lem,,⟶Fin (Step Trans⟶ (Step q r)) = Step (,,⟶Step Trans⟶) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (Intrans⟶Step {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} p) (Step q r)) = Step (,,⟶Step (Intrans⟶Step {_} {_} {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (Intrans⟶Fin {xs} {s} {wc} {rc} {wc'} {rc'} {m} p) (Step q r)) = Step (,,⟶Step (Intrans⟶Fin {_} {_} {xs} {s} {wc} {rc} {wc'} {rc'} {m} p)) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step (Commit _ _) (Step () r))
lem,,⟶Fin (Step Abort (Step q r)) = Step (,,⟶Step Abort) (lem,,⟶Fin (Step q r))
lem,,⟶Fin (Step Giveup (Step q r)) = Step (,,⟶Step Giveup) (lem,,⟶Fin (Step q r))

lem,,⟶Step : {n h : ℕ} {xs xs' : XStmt n} {xm xm' : Stack n h} {s : Stmt n} → ⟨ xs / xm ⟩ ⟶* ⟨ xs' / xm' ⟩ → ⟨ xs ,, s / xm ⟩ ⟶* ⟨ xs' ,, s / xm' ⟩
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
lem,,⟶Step (Step Trans⟶ (Step q r)) = Step (,,⟶Step Trans⟶) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (Intrans⟶Step {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} p) (Step q r)) = Step (,,⟶Step (Intrans⟶Step {_} {_} {xs} {xs'} {s} {wc} {rc} {wc'} {rc'} {m} p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (Intrans⟶Fin {xs} {s} {wc} {rc} {wc'} {rc'} {m} p) (Step q r)) = Step (,,⟶Step (Intrans⟶Fin {_} {_} {xs} {s} {wc} {rc} {wc'} {rc'} {m} p)) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step (Commit _ _) (Step () r))
lem,,⟶Step (Step Abort (Step q r)) = Step (,,⟶Step Abort) (lem,,⟶Step (Step q r))
lem,,⟶Step (Step Giveup (Step q r)) = Step (,,⟶Step Giveup) (lem,,⟶Step (Step q r))

concat* : {n h : ℕ}{c c' c'' : Cfg n h} → c ⟶* c' → c' ⟶* c'' → c ⟶* c''
concat* Finish       q = q
concat* (Step p₁ p₂) q = Step p₁ (concat* p₂ q)

snoc :  {n h : ℕ}{c c' c'' : Cfg n h} → c ⟶* c' → c' ⟶ c'' → c ⟶* c''
snoc Finish      q = Step q Finish
snoc (Step p ps) q = Step p (snoc ps q)

lem0 : {n h : ℕ} → (wc rc : Cache n) → (xm : Stack n h) → {A : Set} → (e : Exp n A) → 
   ∃ λ rc' → ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc ≪ rc' ≪ xm
lem0 _  _  _  (V _)     = _ , refl
lem0 _  rc _  (N _)     = rc , refl
lem0 wc rc xm (y :+ y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))
lem0 wc rc xm (y :- y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))
lem0 wc rc xm (y :× y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))
lem0 _  _  _  true      = _ , refl
lem0 _  _  _  false     = _ , refl
lem0 wc rc xm (¬ e)     = _ , proj₂ (lem0 wc rc xm e)
lem0 wc rc xm (y == y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))
lem0 wc rc xm (y <= y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))
lem0 wc rc xm (y :∨ y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))
lem0 wc rc xm (y :∧ y') = 
  proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') , 
  subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc ≪ proj₁ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y') ≪ xm) (sym (proj₂ (lem0 _ _ xm y))) (proj₂ (lem0 _ _ xm y'))

lem1 : {n h : ℕ} {wc rc : Cache n} {xm : Stack n h} {xm' : Stack n (suc h)}{xs xs' : XStmt n} →
      ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / xm' ⟩ → (∃₂ λ wc' rc' → xm' ≡ wc' ≪ rc' ≪ xm)
lem1 (,,⟶Fin Skip⟶) = _ , _ , refl
lem1 {_} {_} {wc} {rc} {xm} {.(⟦ b ⟧₂ (wc ≪ rc ≪ xm))} {While b do _ ,, s} {.(emb s)} (,,⟶Fin (While⟶False y)) = 
  wc , lem0 _ _ xm b
lem1 {_} {_} {wc} {rc} {xm} {.(write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) (⟦ a ⟧₂ (wc ≪ rc ≪ xm)))} {(x := a) ,, s} {.(emb s)} (,,⟶Fin :=⟶) =
  wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc , 
  proj₁ (lem0 wc rc xm a) , 
  subst (λ m → write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc ≪ proj₁ (lem0 wc rc xm a) ≪ xm) (sym (proj₂ (lem0 _ _ xm a))) refl
lem1 {_} {_} {wc} {rc} {xm} {.(wcmerge wc' wc ≪ rcmerge rc' wc rc ≪ xm)} {Trycommit _ wc' rc' ,, s} {.(emb s)} (,,⟶Fin (Commit .(wc ≪ rc ≪ xm) y)) = 
  wcmerge wc' wc , rcmerge rc' wc rc , refl
lem1 (,,⟶Step y) = lem1 y

lem1 (∥⟶₁Fin Skip⟶) = _ , _ , refl
lem1 {_} {_} {wc} {rc} {xm} {.(⟦ b ⟧₂ (wc ≪ rc ≪ xm))} {While b do _ ∥ xs} {.xs} (∥⟶₁Fin (While⟶False y)) = wc , proj₁ (lem0 _ _ xm b) , proj₂ (lem0 _ _ xm b)
lem1 {_} {_} {wc} {rc} {xm} {.(write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) (⟦ a ⟧₂ (wc ≪ rc ≪ xm)))} {(x := a) ∥ xs} {.xs} (∥⟶₁Fin :=⟶) = 
  wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc , 
  proj₁ (lem0 wc rc xm a) , 
  subst (λ m → write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc ≪ proj₁ (lem0 wc rc xm a) ≪ xm) (sym (proj₂ (lem0 _ _ xm a))) refl
lem1 {_} {_} {wc} {rc} {xm} {._} {Trycommit _ wc' rc' ∥ xs} {.xs} (∥⟶₁Fin (Commit ._ y)) = wcmerge wc' wc , rcmerge rc' wc rc , refl

lem1 (∥⟶₁Step y) = lem1 y

lem1 (∥⟶₂Fin Skip⟶) = _ , _ , refl
lem1 {_} {_} {wc} {rc} {xm} {._} {xs ∥ While b do _} {._} (∥⟶₂Fin (While⟶False y)) = wc , lem0 _ _ xm b
lem1 {_} {_} {wc} {rc} {xm} {._} {xs ∥ (x := a)} {._} (∥⟶₂Fin :=⟶) = 
  wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc , 
  proj₁ (lem0 wc rc xm a) , 
  subst (λ m → write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc ≪ proj₁ (lem0 wc rc xm a) ≪ xm) (sym (proj₂ (lem0 _ _ xm a))) refl
lem1 {_} {_} {wc} {rc} {xm} {._} {xs ∥ Trycommit _ wc' rc'} {._} (∥⟶₂Fin (Commit .(wc ≪ rc ≪ xm) y)) = wcmerge wc' wc , rcmerge rc' wc rc , refl

lem1 (∥⟶₂Step y) = lem1 y

lem1 {_} {_} {wc} {rc} {xm} {.(⟦ b ⟧₂ (wc ≪ rc ≪ xm))} {If b then _ else _} If⟶ = wc , lem0 _ _ xm b
lem1 {_} {_} {wc} {rc} {xm} {.(⟦ b ⟧₂ (wc ≪ rc ≪ xm))} {While b do s} {.(emb s ,, While b do s)} (While⟶True y) = wc , lem0 _ _ xm b

lem1 Trans⟶ = _ , _ , refl
lem1 (Intrans⟶Step _) = _ , _ , refl
lem1 (Intrans⟶Fin _) = _ , _ , refl
lem1 Abort = _ , _ , refl
lem1 Giveup = _ , _ , refl

rcmerge≡∅ : {n : ℕ} (c c' : Cache n) → rcmerge ∅ c' c ≡ c
rcmerge≡∅ [] _ = refl
rcmerge≡∅ (_ ∷ xs) (_ ∷ xs') rewrite rcmerge≡∅ xs xs' = refl

mem≡' : {n h : ℕ}{xm xm' : Stack n h}{wc wc' rc rc' : Cache n} → (wc ≪ rc ≪ xm) ≡ (wc' ≪ rc' ≪ xm') → wc ≡ wc' × rc ≡ rc' × xm ≡ xm'
mem≡' refl = refl , refl , refl

lem2 : {n h : ℕ}{rc rc' wc : Cache n}{xm : Stack n h}
       (y : Var n) → rcmerge (∅ [ y ]≔ just (read y (wc ≪ rc ≪ xm))) wc rc ≡ rc' → 
       (x : Var n) {v : ℕ} → 
       lookup x rc ≡ just v →
       lookup x rc' ≡ just v
lem2 {zero} () _ () _
lem2 {suc n} {h} {nothing ∷ _}                              zero    _    zero    ()
lem2 {suc n} {h} {just _ ∷ _}  {just ._ ∷ ._} {nothing ∷ _} zero    refl zero    refl = refl
lem2 {suc n} {h} {just _ ∷ _}  {nothing ∷ _}  {nothing ∷ _} zero    ()   zero    _
lem2 {suc n} {h} {just _ ∷ _}  {just ._ ∷ ._} {just _ ∷ _}  zero    refl zero    refl = refl
lem2 {suc n} {h} {_ ∷ rc}      {._ ∷ ._}      {_ ∷ wc}      zero    refl (suc x) q    rewrite rcmerge≡∅ rc wc = q
lem2 {suc n} {h} {_ ∷ _}       {._ ∷ ._}      {_ ∷ _}       (suc y) refl zero    q    = q
lem2 {suc n} {h} {_ ∷ _}       {._ ∷ ._}      {_ ∷ _}       (suc y) refl (suc x) q    = lem2 y refl x q

expinvar-wc : {n : ℕ}{wc rc wc' rc' : Cache n} {h : ℕ}{xm' : Stack n h} → (xm : Stack n h) → {A : Set} → (b : Exp n A) → ⟦ b ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm' → wc ≡ wc'
expinvar-wc               _  (V y)     refl = refl
expinvar-wc               _  (N y)     refl = refl
expinvar-wc {_} {wc} {rc} xm (y :+ y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ :+ _)  _ | refl = refl
expinvar-wc {_} {wc} {rc} xm (y :- y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ :- _)  _ | refl = refl
expinvar-wc {_} {wc} {rc} xm (y :× y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ :× _)  _ | refl = refl
expinvar-wc               _  true      refl = refl
expinvar-wc               _  false     refl = refl
expinvar-wc               xm (¬ y)     p    = expinvar-wc xm y p
expinvar-wc {_} {wc} {rc} xm (y == y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ == _)  _ | refl = refl
expinvar-wc {_} {wc} {rc} xm (y <= y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ <= _)  _ | refl = refl
expinvar-wc {_} {wc} {rc} xm (y :∨ y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ :∨ _)  _ | refl = refl
expinvar-wc {_} {wc} {rc} xm (y :∧ y') p with trans (sym p) (trans (cong ⟦ y' ⟧₂ (proj₂ (lem0 wc rc xm y))) (proj₂ (lem0 wc (proj₁ (lem0 wc rc xm y)) xm y')))
expinvar-wc {_} {_}  {_}  _  (_ :∧ _)  _ | refl = refl

expinvar-rc : {n : ℕ}{wc rc wc' rc' : Cache n}{h : ℕ}{A : Set} (e : Exp n A) (xm : Stack n h) → 
  ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm → (x : Var n) → {v : ℕ} → lookup x rc ≡ just v → lookup x rc' ≡ just v
expinvar-rc {zero} (V ()) _ _ () _
expinvar-rc {suc _} {just _ ∷ _}  {just _ ∷ _}  (V zero)    _  refl zero        refl = refl
expinvar-rc {suc _} {nothing ∷ _} {just _ ∷ _}  (V zero)    _  refl zero        refl = refl
expinvar-rc {suc _} {_}           {nothing ∷ _} (V zero)    _  _    zero        ()
expinvar-rc {suc _} {_ ∷ _}       {_ ∷ _}       (V zero)    _  refl (suc x) {v} q    = subst (λ c → lookup x c ≡ just v) (sym (rcmerge≡∅ _ _)) q
expinvar-rc {suc _} {_ ∷ _}       {_ ∷ _}       (V (suc _)) _  refl zero        q    = q
expinvar-rc {suc _} {_ ∷ _}       {_ ∷ _}       (V (suc y)) xm refl (suc x)     q    = expinvar-rc (V y) (peel xm) refl x q
expinvar-rc (N y) xm refl x q = q
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y :+ y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y :- y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y :× y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)
expinvar-rc true xm refl x q = q
expinvar-rc false xm refl x q = q
expinvar-rc (¬ y) xm p x q = expinvar-rc y xm p x q
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y == y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y <= y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y :∨ y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)
expinvar-rc {_} {wc} {rc} {wc'} {rc'} (y :∧ y') xm p x q with lem0 wc rc xm y
... | _ , r = expinvar-rc y' xm (subst (λ m → ⟦ y' ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p) x (expinvar-rc y xm r x q)

expinvar : {n h : ℕ}{wc wc' rc rc' : Cache n}{A : Set} (e : Exp n A) (xm : Stack n h) → 
  ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm → rc' ≺ xm →
  wc' ≡ wc × rc ≺ xm

expinvar (V y) xm refl q = refl , λ x p → q x (lem2 y refl x p)

expinvar (N y) xm refl q = refl , q

expinvar {_} {_} {wc} {_}  {rc} {_}  (e₁ :+ _)  xm _ _ with lem0 wc rc xm e₁
expinvar {_} {_} {wc} {_}  {_}  {_}  (_  :+ e₂) xm _ _ | rc″ , _ with lem0 wc rc″ xm e₂ 
expinvar {_} {_} {_}  {_}  {_}  {_}  (_  :+ e₂) xm p _ | _ , r | _ , s with trans (sym p) (trans (cong (λ xm → ⟦ e₂ ⟧₂ xm) r) s)
expinvar {_} {_} {_}  {._} {_}  {._} (e₁ :+ e₂) xm _ q | _ , r | _ , s | refl = refl , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s q)))

expinvar {n} {h} {wc} {wc'} {rc} {rc'} (e₁ :- e₂) xm p q with lem0 wc rc xm e₁
... | rc'' , r with lem0 wc rc'' xm e₂
... | _    , s = proj₁ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)) , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s (λ x' {v} → subst (λ c → lookup x' c ≡ just v → v ≡ read x' xm) (proj₁ (proj₂ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)))) (q x')))))
expinvar {n} {h} {wc} {wc'} {rc} {rc'} (e₁ :× e₂) xm p q with lem0 wc rc xm e₁
... | rc'' , r with lem0 wc rc'' xm e₂
... | _    , s = proj₁ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)) , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s (λ x' {v} → subst (λ c → lookup x' c ≡ just v → v ≡ read x' xm) (proj₁ (proj₂ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)))) (q x')))))
expinvar true xm refl q = refl , q
expinvar false xm refl q = refl , q
expinvar (¬ e) xm p q = expinvar e xm p q
expinvar {n} {h} {wc} {wc'} {rc} {rc'} (e₁ == e₂) xm p q with lem0 wc rc xm e₁
... | rc'' , r with lem0 wc rc'' xm e₂
... | _    , s = proj₁ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)) , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s (λ x' {v} → subst (λ c → lookup x' c ≡ just v → v ≡ read x' xm) (proj₁ (proj₂ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)))) (q x')))))
expinvar {n} {h} {wc} {wc'} {rc} {rc'} (e₁ <= e₂) xm p q with lem0 wc rc xm e₁
... | rc'' , r with lem0 wc rc'' xm e₂
... | _    , s = proj₁ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)) , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s (λ x' {v} → subst (λ c → lookup x' c ≡ just v → v ≡ read x' xm) (proj₁ (proj₂ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)))) (q x')))))
expinvar {n} {h} {wc} {wc'} {rc} {rc'} (e₁ :∨ e₂) xm p q with lem0 wc rc xm e₁
... | rc'' , r with lem0 wc rc'' xm e₂
... | _    , s = proj₁ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)) , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s (λ x' {v} → subst (λ c → lookup x' c ≡ just v → v ≡ read x' xm) (proj₁ (proj₂ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)))) (q x')))))
expinvar {n} {h} {wc} {wc'} {rc} {rc'} (e₁ :∧ e₂) xm p q with lem0 wc rc xm e₁
... | rc'' , r with lem0 wc rc'' xm e₂
... | _    , s = proj₁ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)) , proj₂ (expinvar e₁ xm r (proj₂ (expinvar e₂ xm s (λ x' {v} → subst (λ c → lookup x' c ≡ just v → v ≡ read x' xm) (proj₁ (proj₂ (mem≡' (trans (sym (subst (λ m → ⟦ e₂ ⟧₂ m ≡ wc' ≪ rc' ≪ xm) r p)) s)))) (q x')))))


expinvar₂ :  {n h : ℕ}{wc wc' rc rc' : Cache n}{A : Set} (e : Exp n A) (xm : Stack n h) → 
  ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm → rc ≺ xm → rc' ≺ xm
expinvar₂ {zero} (V ()) _ _ _ () _
expinvar₂ {suc _} {_} {just _ ∷ _}  {._} {._ ∷ _}      {._} (V zero)    _ refl q zero    refl = q zero refl
expinvar₂ {suc _} {_} {nothing ∷ _} {._} {just ._ ∷ _} {._} (V zero)    _ refl q zero    refl = q zero refl
expinvar₂ {suc _} {_} {nothing ∷ _} {._} {nothing ∷ _} {._} (V zero)    _ refl _ zero    refl = refl
expinvar₂ {suc _} {_} {just _ ∷ _}  {._} {._ ∷ _}      {._} (V (suc _)) _ refl q zero    refl = q zero refl
expinvar₂ {suc _} {_} {nothing ∷ _} {._} {._ ∷ _}      {._} (V (suc _)) _ refl q zero    refl = q zero refl
expinvar₂ {suc _} {_} {_ ∷ wc}      {._} {_ ∷ rc}      {._} (V zero)    _ refl q (suc x) {v} r = q (suc x) (subst (λ rc → lookup x rc ≡ just v) (rcmerge≡∅ rc wc) r)
expinvar₂ {suc _} {_} {wv ∷ wc} {._} {rv ∷ rc} {._} (V (suc y)) xm refl q (suc x) r = trans (expinvar₂ (V y) (peel xm) refl (λ x p → trans (q (suc x) p) (sym (lemmapeel xm x))) x r) (lemmapeel xm x)
expinvar₂ (N y) xm refl q x r = q x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y :+ y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y :- y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y :× y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r
expinvar₂ true xm refl q x r = q x r
expinvar₂ false xm refl q x r = q x r
expinvar₂ (¬ y) xm p q x r = expinvar₂ y xm p (λ x → q x) x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y == y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y <= y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y :∨ y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r
expinvar₂ {n} {h} {wc} {wc'} {rc} {rc'} (y :∧ y') xm p q x r with lem0 wc rc xm y
... | rc'' , s with lem0 wc rc'' xm y' 
... | _ , t = expinvar₂ y' xm (subst (λ xm' → ⟦ y' ⟧₂ xm' ≡ wc' ≪ rc' ≪ xm) s p) (expinvar₂ y xm s q) x r

finsameh : {n h : ℕ} {xs : XStmt n} {xm : Stack n h} {wc rc : Cache n} {xm'' : Stack n (suc h)} → ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xm'' ⟩ → 
    ∃₂ λ wc' rc' → xm'' ≡ wc' ≪ rc' ≪ xm
finsameh Skip⟶ = _ , _ , refl
finsameh {n} {h} {While b do _} {xm} {wc} {rc} (While⟶False y) = wc , lem0 wc rc xm b
finsameh {n} {h} {x := a} {xm} {wc} {rc} :=⟶ with lem0 wc rc xm a 
... | rc' , p = wcmerge (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) wc , rc' , cong (λ m → write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m) p
finsameh {n} {h} {Trycommit s wc0 rc0} {xm} {wc} {rc} (Commit ._ y) = wcmerge wc0 wc , rcmerge rc0 wc rc , refl

stepsameh : {n h : ℕ} {xs : XStmt n} {xm : Stack n h} {wc rc : Cache n} {xs' : XStmt n} {xm'' : Stack n (suc h)} → ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / xm'' ⟩ → 
    ∃₂ λ wc' rc' → xm'' ≡ wc' ≪ rc' ≪ xm
stepsameh (,,⟶Fin y) = finsameh y
stepsameh (,,⟶Step y) = stepsameh y
stepsameh (∥⟶₁Fin y) = finsameh y
stepsameh (∥⟶₁Step y) = stepsameh y
stepsameh (∥⟶₂Fin y) = finsameh y
stepsameh (∥⟶₂Step y) = stepsameh y
stepsameh {n} {h} {If b then s₁ else s₂} {xm} {wc} {rc} If⟶ = wc , lem0 wc rc xm b
stepsameh {n} {h} {While b do s} {xm} {wc} {rc} (While⟶True y) = wc , lem0 wc rc xm b
stepsameh Trans⟶ = _ , _ , refl
stepsameh (Intrans⟶Step _) = _ , _ , refl
stepsameh (Intrans⟶Fin _) = _ , _ , refl
stepsameh Abort = _ , _ , refl
stepsameh Giveup = _ , _ , refl

stepcfg : {n h : ℕ} {s : XStmt n} {xm : Stack n h} {c c' : Cfg n h} → ⟨ s / xm ⟩ ⟶ c → c ⟶ c' → ∃₂ λ s' xm' → c ≡ ⟨ s' / xm' ⟩
stepcfg Skip⟶            ()
stepcfg (,,⟶Fin _)       _  = _ , _ , refl
stepcfg (,,⟶Step _)      _  = _ , _ , refl
stepcfg (∥⟶₁Fin _)      _  = _ , _ , refl
stepcfg (∥⟶₁Step _)     _  = _ , _ , refl
stepcfg (∥⟶₂Fin _)      _  = _ , _ , refl
stepcfg (∥⟶₂Step _)     _  = _ , _ , refl
stepcfg If⟶              _  = _ , _ , refl
stepcfg (While⟶True y)   _  = _ , _ , refl
stepcfg (While⟶False y)  ()
stepcfg :=⟶              ()
stepcfg Trans⟶           _  = _ , _ , refl
stepcfg (Intrans⟶Step _) _  = _ , _ , refl
stepcfg (Intrans⟶Fin _)  _  = _ , _ , refl
stepcfg (Commit _ _)      ()
stepcfg Abort             _  = _ , _ , refl
stepcfg Giveup            _  = _ , _ , refl
