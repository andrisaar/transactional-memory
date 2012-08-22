module CacheProperties where

open import Data.Nat
open import Data.Fin hiding (_≺_)
open import Data.Vec
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Core
open import Lazy

_⊆_ : ∀{n} → Cache n → Cache n → Set
_⊆_ {n} c₁ c₂ = ∀{v} → (x : Var n) → lookup x c₁ ≡ just v → lookup x c₂ ≡ just v

sub-id : ∀{n}{c : Cache n} → c ⊆ c
sub-id x p = p

sub-trans : ∀{n}{c₁ c₂ c₃ : Cache n} → c₁ ⊆ c₂ → c₂ ⊆ c₃ → c₁ ⊆ c₃
sub-trans p q x r = q x (p x r)

subset-consistent : ∀{n h}{rc rc'}{xm : Stack n h} → rc' ≺ xm → rc ⊆ rc' → rc ≺ xm
subset-consistent p q x r = p x (q x r)

subset-rc : ∀{n wc rc wc' rc'}{h}{xm xm' : Stack n h}{A : Set} → (e : Exp n A) → ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc' ≪ rc' ≪ xm' → rc ⊆ rc'
subset-rc {wc = []} _ _ () _
subset-rc {wc = nothing ∷ wc} {nothing ∷ rc} (V zero)    refl zero    ()
subset-rc {wc = nothing ∷ wc} {nothing ∷ rc} (V zero)    refl (suc x) q rewrite rcmerge≡∅ rc wc = q
subset-rc {wc = nothing ∷ wc} {just _  ∷ rc} (V zero)    refl x       q rewrite rcmerge≡∅ rc wc = q
subset-rc {wc = just _  ∷ wc} {_       ∷ rc} (V zero)    refl x       q rewrite rcmerge≡∅ rc wc = q
subset-rc {wc = _       ∷ _ } {_       ∷ _ } (V (suc _)) refl zero    q = q
subset-rc {wc = _       ∷ _ } {_       ∷ _ } (V (suc y)) refl (suc x) q = subset-rc (V y) refl x q
subset-rc                                    (N _)       refl _       q = q
subset-rc {wc = wc} {rc} {xm = xm} (e :+ e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)
subset-rc {wc = wc} {rc} {xm = xm} (e :- e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)
subset-rc {wc = wc} {rc} {xm = xm} (e :× e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)
subset-rc true refl x q = q
subset-rc false refl x q = q
subset-rc (¬ e) p x q = subset-rc e p x q
subset-rc {wc = wc} {rc} {xm = xm} (e == e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)
subset-rc {wc = wc} {rc} {xm = xm} (e <= e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)
subset-rc {wc = wc} {rc} {xm = xm} (e :∨ e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)
subset-rc {wc = wc} {rc} {xm = xm} (e :∧ e₁) p x q with lem0 wc rc xm e
... | rc'' , r rewrite r = subset-rc e₁ p x (subset-rc e r x q)

private
  helper : ∀{n wc rc rc' v} → (x : Var n) → lookup x rc ≡ just v → lookup x (rcmerge rc' wc rc) ≡ just v
  helper {zero} () _
  helper {wc = _ ∷ _}       {rc = _ ∷ _}       {rc' = nothing ∷ _} zero    p = p
  helper {wc = nothing ∷ _} {rc = nothing ∷ _} {rc' = just _ ∷ _}  zero    ()
  helper {wc = just _ ∷ _}  {rc = nothing ∷ _} {rc' = just _ ∷ _}  zero    ()
  helper {wc = nothing ∷ _} {rc = just _ ∷ _}  {rc' = just _ ∷ _}  zero    p = p
  helper {wc = just _ ∷ _}  {rc = just _ ∷ _}  {rc' = just _ ∷ _}  zero    p = p
  helper {wc = _ ∷ wc}      {rc = _ ∷ rc}      {rc' = _ ∷ rc'}     (suc x) p = helper x p

subset-rc-fin : ∀{n wc rc wc' rc'}{h}{xm xm' : Stack n h}{xm₂ : Stack n (suc h)}{xs : XStmt n} → ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xm₂ ⟩ → xm₂ ≡ wc' ≪ rc' ≪ xm' → rc ⊆ rc'
subset-rc-fin Skip⟶ refl x q = q
subset-rc-fin (While⟶False {b = b} _) p x q = subset-rc b p x q
subset-rc-fin {n} {wc} {rc} {xm = xm} (:=⟶ {a = a}) p x₁ q with lem0 wc rc xm a
... | rc'' , s rewrite s with p
...    | refl = subset-rc a s x₁ q
subset-rc-fin {n} {wc} {rc} {._} {._} {h} {xm} (Commit {_} {wc'} {rc'} .(wc ≪ rc ≪ xm) p) refl x q = helper x q

subset-rc-step : ∀{n wc rc wc' rc'}{h}{xm xm' : Stack n h}{xm₂ : Stack n (suc h)}{xs xs' : XStmt n} → ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / xm₂ ⟩ → xm₂ ≡ wc' ≪ rc' ≪ xm' → rc ⊆ rc'

subset-rc-step (,,⟶Fin p')            p    x q = subset-rc-fin p' p x q
subset-rc-step (,,⟶Step p')           refl x q = subset-rc-step p' refl x q
subset-rc-step (∥⟶₁Fin p')            p    x q = subset-rc-fin p' p x q
subset-rc-step (∥⟶₁Step p')           refl x q = subset-rc-step p' refl x q
subset-rc-step (∥⟶₂Fin p')            p    x q = subset-rc-fin p' p x q
subset-rc-step (∥⟶₂Step p')           refl x q = subset-rc-step p' refl x q
subset-rc-step (If⟶ {b = b})          p    x q = subset-rc b p x q
subset-rc-step (While⟶True {b = b} _) p    x q = subset-rc b p x q
subset-rc-step Trans⟶                 refl _ q = q
subset-rc-step (Intrans⟶Step _)       refl _ q = q
subset-rc-step (Intrans⟶Fin _)        refl _ q = q
subset-rc-step Abort                    refl _ q = q
subset-rc-step Giveup                   refl _ q = q

