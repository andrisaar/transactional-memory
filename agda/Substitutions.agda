module Substitutions where

open import Data.Bool
open import Data.Nat
open import Data.Vec public using (_∷_; [])
open import Data.Maybe.Core
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Core
open import Lazy

exp-subst-mem₂ : {n : ℕ}{wc rc wc' rc' : Cache n} {h : ℕ} → (xm : Stack n h) → {h' : ℕ} → (xm' : Stack n h') → {A : Set} → (e : Exp n A) → 
   ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm → 
   rc' ≺ xm' → 
   ⟦ e ⟧₂ (wc ≪ rc ≪ xm') ≡ wc' ≪ rc' ≪ xm'
exp-subst-mem₂ {zero}                              _  _   (V ())      _    _
exp-subst-mem₂ {suc _} {just _ ∷ _}  {_ ∷ _}       _  _   (V zero)    refl _ = refl
exp-subst-mem₂ {suc _} {nothing ∷ _} {just rv ∷ _} _  _   (V zero)    refl _ = refl
exp-subst-mem₂ {suc _} {nothing ∷ w} {nothing ∷ r} _  xm' (V zero)    refl q rewrite q zero refl = refl
exp-subst-mem₂ {suc _} {wv ∷ wc}     {rv ∷ rc}     xm xm' (V (suc x)) refl q with mem≡' (exp-subst-mem₂ (peel xm) (peel xm') (V x) refl (λ x' p → trans (q (suc x') p) (sym (lemmapeel xm' x'))))
... | refl , p , refl rewrite p = refl
exp-subst-mem₂ xm xm' (N _) refl _ = refl
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ :+ e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ :- e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ :× e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s
exp-subst-mem₂ xm xm' true refl q = refl
exp-subst-mem₂ xm xm' false refl q = refl
exp-subst-mem₂ xm xm' (¬ y) p q = exp-subst-mem₂ xm xm' y p q
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ == e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ <= e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ :∧ e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s
exp-subst-mem₂ {_} {wc} {rc} xm xm' (e₁ :∨ e₂) p q with (lem0 wc rc xm e₁)
... | rc'' , r with exp-subst-mem₂ xm xm' e₂ (trans (sym (cong ⟦ e₂ ⟧₂ r)) p) q
...   | s = trans (cong ⟦ e₂ ⟧₂ (exp-subst-mem₂ xm xm' e₁ r (proj₂ (expinvar e₂ xm' s q)))) s

exp-subst-mem₁ : {n h h' : ℕ}{wc wc' rc rc' : Cache n} → (xm : Stack n h) → (xm' : Stack n h') → {A : Set} → (e : Exp n A) → 
   ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm → 
   rc' ≺ xm' → 
   ⟦ e ⟧₁ (wc ≪ rc ≪ xm) ≡ ⟦ e ⟧₁ (wc ≪ rc ≪ xm')
exp-subst-mem₁ {zero} _ _ (V ()) _ _
exp-subst-mem₁ {wc = just _  ∷ _}  {rc = _       ∷ _}  xm xm' (V zero)    _    _ = refl
exp-subst-mem₁ {wc = nothing ∷ _}  {rc = just _  ∷ _}  xm xm' (V zero)    _    _ = refl
exp-subst-mem₁ {wc = nothing ∷ _}  {rc = nothing ∷ _}  xm xm' (V zero)    refl q = q zero refl
exp-subst-mem₁ {wc =       _ ∷ wc} {rc = _       ∷ rc} xm xm' (V (suc x)) refl q = exp-subst-mem₁ (peel xm) (peel xm') (V x) refl (λ x p → trans (q (suc x) p) (sym (lemmapeel xm' x)))
exp-subst-mem₁ xm xm' (N y) refl q = refl

exp-subst-mem₁ {wc = wc} {rc = rc} xm xm' (e₁ :+ e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl
exp-subst-mem₁ {wc = wc} {rc = rc} xm xm' (e₁ :- e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl
exp-subst-mem₁ {wc = wc} {rc = rc} xm xm' (e₁ :× e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl
exp-subst-mem₁ xm xm' true refl q = refl
exp-subst-mem₁ xm xm' false refl q = refl
exp-subst-mem₁ xm xm' (¬ e) p q rewrite exp-subst-mem₁ xm xm' e p q = refl

exp-subst-mem₁ {wc = wc} {rc = rc} xm xm' (e₁ == e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl

exp-subst-mem₁  {wc = wc} {rc = rc} xm xm' (e₁ <= e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl

exp-subst-mem₁ {wc = wc} {rc = rc} xm xm' (e₁ :∨ e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl

exp-subst-mem₁ {wc = wc} {rc = rc} xm xm' (e₁ :∧ e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r with expinvar e₂ xm' (exp-subst-mem₂ xm xm' e₂ p q) q
...    | refl , s rewrite exp-subst-mem₁ xm xm' e₁ r s | 
                          exp-subst-mem₂ xm xm' e₁ r s |
                          exp-subst-mem₁ xm xm' e₂ p q = refl

