module LazyProperties where

open import Data.Bool
open import Data.Nat
open import Data.Vec public using (_∷_; [])
open import Data.Maybe.Core
open import Data.Product
open import Function

open import Relation.Binary.PropositionalEquality

open import Core
open import Lazy
open import Substitutions

private
  helper : {n : ℕ} {rc' wc rc : Cache n} {h : ℕ} → {xm : Stack n h} → rcmerge rc' wc rc ≺ xm → rc ≺ xm
  helper {zero}                                            _ ()      _
  helper {suc n} {_ ∷ _}       {_ ∷ _}       {nothing ∷ _} q zero  ()
  helper {suc n} {nothing ∷ _} {_ ∷ _}       {just _ ∷ _}  q zero  r  = q zero r
  helper {suc n} {just _ ∷ _}  {nothing ∷ _} {just _ ∷ _}  q zero  r  = q zero r
  helper {suc n} {just _ ∷ _}  {just _ ∷ _}  {just _ ∷ _}  q zero  r  = q zero r
  helper {suc n} {_ ∷ rc'}     {_ ∷ wc}      {_ ∷ rc} {h} {xm} q (suc x) r rewrite sym (lemmapeel xm x) = helper {xm = peel xm} (λ x {v} → subst (λ r → lookup x (rcmerge rc' wc rc) ≡ just v → v ≡ r) (sym (lemmapeel xm x)) (q (suc x))) x r
  
  rcFin' : {n : ℕ} {xs : XStmt n} {wc rc : Cache n} {h : ℕ} {xm : Stack n h} {wc' rc' : Cache n} {h' : ℕ} → (xm' : Stack n h') → {xm₂ : Stack n (suc h) } → 
    ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xm₂ ⟩  →
    xm₂ ≡ wc' ≪ rc' ≪ xm → 
    rc' ≺ xm' → 
    rc ≺ xm'
  rcFin'                    xm' Skip⟶           refl   q = q
  rcFin' {_} {While b do _} xm' (While⟶False y) p      q = proj₂ (expinvar b xm' (exp-subst-mem₂ _ _ b p q) q)

  rcFin' {_} {_ := a} {wc} {rc} {_} {xm}             xm' :=⟶ _ _ with lem0 wc rc xm a
  rcFin' {_} {y := a} {wc} {rc} {_} {xm} {wc'} {rc'} xm' :=⟶ p _ | _ , s  with subst (λ m → write (∅ [ y ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wc' ≪ rc' ≪ xm) s p
  rcFin' {_} {_ := a}                                xm' :=⟶ _ q | _ , s | refl = proj₂ (expinvar a xm' (exp-subst-mem₂ _ _ a s q) q)

  rcFin' {xm = xm} xm' (Commit ._ _) refl q = helper {xm = xm'} q

  rcStep' :  {n : ℕ}{xs : XStmt n}{h h' : ℕ} {xm : Stack n h} → (xm' : Stack n h') → {xs' : XStmt n} {wc wc' rc rc' : Cache n} {xm₂ : Stack n (suc h) } → 
    ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / xm₂ ⟩  →
    xm₂ ≡ wc' ≪ rc' ≪ xm → 
    rc' ≺ xm' → 
    rc ≺ xm'
  rcStep' xm' (,,⟶Fin y  )     p    q = rcFin' xm' y p q
  rcStep' xm' (,,⟶Step y )     p    q = rcStep' xm' y p q
  rcStep' xm' (∥⟶₁Fin y)      p    q = rcFin' xm' y p q
  rcStep' xm' (∥⟶₁Step y)     p    q = rcStep' xm' y p q
  rcStep' xm' (∥⟶₂Fin y)      p    q = rcFin' xm' y p q
  rcStep' xm' (∥⟶₂Step y)     p    q = rcStep' xm' y p q
  rcStep' {_} {If b then _ else _} xm' If⟶ p q = proj₂ (expinvar b xm' (exp-subst-mem₂ _ _ b p q) q)
  rcStep' {_} {While b do _} xm' (While⟶True y) p q = proj₂ (expinvar b xm' (exp-subst-mem₂ _ _ b p q) q)
  rcStep' xm' Trans⟶           refl q = q
  rcStep' xm' (Intrans⟶Step y) refl q = q
  rcStep' xm' (Intrans⟶Fin y)  refl q = q
  rcStep' xm' Abort             refl q = q
  rcStep' xm' Giveup            refl q = q

rcFin :  {n h h' : ℕ} {wc wc' rc rc' : Cache n} {xm : Stack n h} {xm' : Stack n h'} {xs : XStmt n} → 
  ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ wc' ≪ rc' ≪ xm ⟩  →
  rc' ≺ xm' → 
  rc ≺ xm'
rcFin {xm' = xm'} step p = rcFin' xm' step refl p

rcStep :  {n h h' : ℕ} {wc wc' rc rc' : Cache n} {xm : Stack n h} {xm' : Stack n h'} {xs xs' : XStmt n} → 
  ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / wc' ≪ rc' ≪ xm ⟩  →
  rc' ≺ xm' → 
  rc ≺ xm'
rcStep {xm' = xm'} step p = rcStep' xm' step refl p

private
  helper' : {n h : ℕ} {trc wc rc : Cache n} {xm : Stack n h} → rc ≺ xm → trc ≺ (wc ≪ rc ≪ xm) → rcmerge trc wc rc ≺ xm
  helper' {zero}                                                _ _ ()   _
  helper' {suc _} {_} {nothing ∷ _} {_ ∷ _}       {._ ∷ _}      p _ zero    refl = p zero refl
  helper' {suc _} {_} {just ._ ∷ _} {nothing ∷ _} {nothing ∷ _} _ q zero    refl = q zero refl
  helper' {suc _} {_} {just _ ∷ _}  {nothing ∷ _} {just ._ ∷ _} p _ zero    refl = p zero refl
  helper' {suc _} {_} {just _ ∷ _}  {just _ ∷ _}  {._ ∷ _}      p _ zero    refl = p zero refl
  helper' {suc _} {_} {_ ∷ _}       {_ ∷ _}       {_ ∷ _} {xm = xm} p q (suc x) r rewrite sym (lemmapeel xm x) = helper' (λ x s → trans (p (suc x) s) (sym (lemmapeel xm x))) (q ∘ suc) x r

  rcFinFwd' : {n h : ℕ} {xm : Stack n h} {xs : XStmt n} {wc rc wc' rc' : Cache n} {xm' : Stack n (suc h) } → 
    ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xm' ⟩  →
    xm' ≡ wc' ≪ rc' ≪ xm → 
    rc ≺ xm → 
    rc' ≺ xm
  rcFinFwd' Skip⟶ refl q = q
  rcFinFwd' {_} {_} {xm} {While b do _} (While⟶False y) p    q = expinvar₂ b xm p q
  
  rcFinFwd' {_} {_} {xm} {_ := a} {wc} {rc}             :=⟶ _ _ with lem0 wc rc xm a
  rcFinFwd' {_} {_} {xm} {y := a} {wc} {rc} {wc'} {rc'} :=⟶ p _ | _ , s with subst (λ m → write (∅ [ y ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wc' ≪ rc' ≪ xm) s p
  rcFinFwd' {_} {_} {xm} {_ := a}                       :=⟶ _ q | _ , s | refl = expinvar₂ a xm s q

  rcFinFwd' (Commit ._ y) refl q = helper' q y

  rcStepFwd' :  {n h : ℕ} {xm : Stack n h} {xs xs' : XStmt n} {wc wc' rc rc' : Cache n} {xm' : Stack n (suc h) } → 
    ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / xm' ⟩  →
    xm' ≡ wc' ≪ rc' ≪ xm → 
    rc ≺ xm → 
    rc' ≺ xm
  rcStepFwd' (,,⟶Fin y)       p q = rcFinFwd' y p q
  rcStepFwd' (,,⟶Step y)      p q = rcStepFwd' y p q
  rcStepFwd' (∥⟶₁Fin y)      p q = rcFinFwd' y p q
  rcStepFwd' (∥⟶₁Step y)     p q = rcStepFwd' y p q
  rcStepFwd' (∥⟶₂Fin y)      p q = rcFinFwd' y p q
  rcStepFwd' (∥⟶₂Step y)     p q = rcStepFwd' y p q
  rcStepFwd' {_} {_} {_} {If b then _ else _} If⟶ p q = expinvar₂ b _ p q
  rcStepFwd' {_} {_} {_} {While b do _}(While⟶True y) p q = expinvar₂ b _ p q
  rcStepFwd' Trans⟶           refl q = q
  rcStepFwd' (Intrans⟶Step _) refl q = q
  rcStepFwd' (Intrans⟶Fin _)  refl q = q
  rcStepFwd' Abort             refl q = q
  rcStepFwd' Giveup            refl q = q

rcFinFwd : {n h : ℕ} {xm : Stack n h} {xs : XStmt n} {wc wc' rc rc' : Cache n} → 
  ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ wc' ≪ rc' ≪ xm ⟩ → rc ≺ xm → rc' ≺ xm
rcFinFwd step p = rcFinFwd' step refl p

rcStepFwd : {n h : ℕ} {wc wc' rc rc' : Cache n} {xm : Stack n h} {xs xs' : XStmt n} → ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶ ⟨ xs' / wc' ≪ rc' ≪ xm ⟩ → rc ≺ xm → rc' ≺ xm
rcStepFwd step p = rcStepFwd' step refl p

private
  samefin' : {n h : ℕ} {s : XStmt n} {xm : Stack n h} {wc rc wc' rc' : Cache n} {xm' : Stack n h} {xm'' : Stack n (suc h)} → 
    wc' ≪ rc' ≪ xm' ≡ xm'' → ⟨ s / wc ≪ rc ≪ xm ⟩ ⟶* ⟨ xm'' ⟩ → rc ≺ xm → 
    rc' ≺ xm' × xm ≡ xm'
  samefin'                                                         _    (Step _  s₂) _ with s₂
  samefin'                                                         _    (Step s₁ _)  _ | Finish with s₁
  samefin'                                                         refl (Step _  _)  q | Finish | Skip⟶ = q , refl
  samefin' {_} {_} {While b do _} {xm} {wc} {rc}                   _    (Step _  _)  _ | Finish | While⟶False y with lem0 wc rc xm b
  samefin' {_} {_} {While b do _} {xm} {wc} {rc}                   p    (Step _  _)  _ | Finish | While⟶False _ | _ , r with trans p r 
  samefin' {_} {_} {While b do _} {xm} {wc} {rc}                   _    (Step s₁ s₂) q | Finish | While⟶False _ | _ , r | refl = expinvar₂ b xm r q , refl
  samefin' {_} {_} {x := a}       {xm} {wc} {rc} {_}   {_}   {_}   _    (Step _ _)   _ | Finish | :=⟶ with lem0 wc rc xm a
  samefin' {_} {_} {x := a}       {xm} {wc} {rc} {wc'} {rc'} {xm'} p    (Step _ _)   _ | Finish | :=⟶ | _ , r with subst (λ xm₂ → wc' ≪ rc' ≪ xm' ≡ write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) xm₂) r p
  samefin' {_} {_} {x := a}       {xm} {_}  {_}  {._}  {._}  {._}  _    (Step _ _)   q | Finish | :=⟶ | _ , r | refl = expinvar₂ a xm r q , refl
  samefin'                                                         refl (Step _ _)   q | Finish | Commit ._ p = helper' q p , refl
  samefin'                                                         _    (Step s₁ _)  _ | Step s _ with stepcfg s₁ s
  samefin'                                                         _    (Step s₁ _)  _ | Step _ _ | _ , (_ ≪ _ ≪ _) , refl with lem1 s₁
  samefin'                                                         refl (Step s₁ s₂) q | Step _ _ | _ , (._ ≪ ._ ≪ _) , refl | _ , _ , refl = samefin' refl s₂ (rcStepFwd s₁ q)

samefin : {n h : ℕ} {s : XStmt n} {xm : Stack n h} {wc rc wc' rc' : Cache n} {xm' : Stack n h} → ⟨ s / wc ≪ rc ≪ xm ⟩ ⟶* ⟨ wc' ≪ rc' ≪ xm' ⟩ → rc ≺ xm → rc' ≺ xm' × xm ≡ xm'
samefin step p = samefin' refl step p

