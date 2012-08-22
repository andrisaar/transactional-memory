module Dev where

open import Core

open import Lazy renaming (_⟶_ to _⟶w_; _⟶*_ to _⟶w*_; Cfg to XCfg; ⟦_⟧ to w⟦_⟧)
open import Strong renaming (_⟶_ to _⟶s_; _⟶*_ to _⟶s*_; ⟦_⟧ to s⟦_⟧)

--open import Lazy
--open import CacheProperties

open import Data.Product
open import Data.Vec
open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Data.Fin hiding (_≺_)
open import Function

open import Relation.Binary.PropositionalEquality

open import Relation.Nullary.Decidable

open import LazyCorrect hiding (foo')

foo' : {n h : ℕ}{xm : Stack n h}{m : Mem n}{wc rc wc' rc' : Cache n}{xm' : Stack n (suc h)}{xs : XStmt n}{s : Stmt n} →
    ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶w ⟨ xm' ⟩ → xm' ≡ wc' ≪ rc' ≪ xm → xs ≋ s → rc' ≺ (m ◁) →
    ⟨ s / merge wc m ⟩ ⟶s* ⟨ merge wc' m ⟩

foo' Skip⟶           refl Skip≋ _ = Step Skip⟶ Finish

foo' (While⟶False y) p    (While≋ {b} {s}) r with expinvar-wc _ b p
... | refl = Step (While⟶False (subst (T ∘ not) (bar b p r) y)) Finish

foo' {_} {_} {xm} {_} {wc} {rc}             :=⟶ _ (:=≋ {_} {a}) _ with lem0 wc rc xm a
foo' {_} {_} {xm} {_} {wc} {rc} {wc'} {rc'} :=⟶ p (:=≋ {x} {a}) _ | _  , w with subst (λ m → write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wc' ≪ rc' ≪ xm) w p
foo' {_} {_} {xm} {m} {wc} {rc}             :=⟶ p (:=≋ {x} {a}) q | ._ , w | refl = Step (subst (λ m' → ⟨ x := a / merge wc m ⟩ ⟶s ⟨ m' ⟩) (subst (λ v → merge wc m [ x ]≔ s⟦ a ⟧ (merge wc m) ≡ merge (wcmerge (∅ [ x ]≔ just v) wc) m) (sym (bar a w q)) (mc x)) :=⟶) Finish

foo' {_} {_} {xm} {m} {wc} {rc} (Commit ._ y) refl (Trycommit≋ {wc0} {rc0} {s} q) r = Step (Trans⟶ (subst (λ m' → ⟨ s / merge wc m ⟩ ⟶s* ⟨ m' ⟩) mt (q (merge wc m) (rcm r y)))) Finish

