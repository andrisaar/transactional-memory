module LazyCorrect where

open import Core
open import Lazy renaming (_⟶_ to _⟶w_; _⟶*_ to _⟶w*_; Cfg to XCfg; ⟦_⟧ to w⟦_⟧)
open import Strong renaming (_⟶_ to _⟶s_; _⟶*_ to _⟶s*_; ⟦_⟧ to s⟦_⟧)

open import Substitutions
open import LazyProperties

open import Function hiding (_⟨_⟩_)
open import Data.Bool
open import Data.Maybe.Core
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

write-same-cons : {n h : ℕ}{xm : Stack n h}{m : Mem n}{x : Var n}{v : ℕ} → xm ≈ m ◁ → (write (∅ [ x ]≔ just v) xm) ≈ (m [ x ]≔ v) ◁
write-same-cons {zero}  {_}     {_} {_} {()} _ ()
write-same-cons {suc n} {zero}  {(_ ∷ _) ◁}                          {_ ∷ _} {zero}  p zero    = refl
write-same-cons {suc n} {zero}  {(_ ∷ m') ◁}                         {_ ∷ m} {zero}  p (suc y) rewrite merge≡ m' = p (suc y)
write-same-cons {suc n} {zero}  {(_ ∷ _) ◁}                          {_ ∷ _} {suc x} p (zero)  = p zero
write-same-cons {suc n} {zero}  {(_ ∷ m') ◁}                         {_ ∷ _} {suc x} p (suc y) = write-same-cons {xm = m' ◁} (p ∘ suc) y
write-same-cons {suc _} {suc _} {(just _ ∷ _)  ≪ (just _ ∷ _)  ≪ _} {_ ∷ _} {zero}  p zero    = refl
write-same-cons {suc _} {suc _} {(just _ ∷ _)  ≪ (nothing ∷ _) ≪ _} {_ ∷ _} {zero}  p zero    = refl
write-same-cons {suc _} {suc _} {(nothing ∷ _) ≪ (_ ∷ _)       ≪ _} {_ ∷ _} {zero}  p zero    = refl
write-same-cons {suc _} {suc _} {(just _ ∷ _)  ≪ (just _ ∷ _)  ≪ _} {_ ∷ _} {suc _} p zero    = p zero
write-same-cons {suc _} {suc _} {(just _ ∷ _)  ≪ (nothing ∷ _) ≪ _} {_ ∷ _} {suc _} p zero    = p zero
write-same-cons {suc _} {suc _} {(nothing ∷ _) ≪ (just _ ∷ _)  ≪ _} {_ ∷ _} {suc _} p zero    = p zero
write-same-cons {suc _} {suc _} {(nothing ∷ _) ≪ (nothing ∷ _) ≪ _} {_ ∷ _} {suc _} p zero    = p zero
write-same-cons {suc _} {suc _} {(_ ∷ wc) ≪ _ ∷ rc ≪ xm}            {_ ∷ m} {zero}  p (suc y) rewrite wcmerge≡ wc = p (suc y)
write-same-cons {suc _} {suc _} {(_ ∷ wc) ≪ (_ ∷ rc) ≪ xm}             {_ ∷ _} {suc _} p (suc y) = write-same-cons {xm = wc ≪ rc ≪ peel xm} (p ∘ suc) y

exp-eval-same : {n h : ℕ}{A : Set} → (a : Exp n A) → (xm : Stack n h) → (m : Mem n) →
  xm ≈ m ◁ → proj₁ (w⟦ a ⟧ xm) ≡ s⟦ a ⟧ m × proj₂ (w⟦ a ⟧ xm) ≈ m ◁
exp-eval-same (V x) xm m p =
  p x , Lemma1 xm (m ◁) (∅ [ x ]≔ just (read x xm)) p (consupdate ∅ xm (consempty xm))
exp-eval-same (N v) xm m p = refl , p
exp-eval-same (a₁ :+ a₂) xm m p with exp-eval-same a₁ xm m p
... | q , r with exp-eval-same a₂ (proj₂ (w⟦ a₁ ⟧ xm)) m r
...    | s , t = cong₂ _+_ q s , t
exp-eval-same (a₁ :- a₂) xm m p with exp-eval-same a₁ xm m p
... | q , r with exp-eval-same a₂ (proj₂ (w⟦ a₁ ⟧ xm)) m r
...    | s , t = cong₂ _∸_ q s , t
exp-eval-same (a₁ :× a₂) xm m p with exp-eval-same a₁ xm m p
... | q , r with exp-eval-same a₂ (proj₂ (w⟦ a₁ ⟧ xm)) m r
...    | s , t = cong₂ _*_ q s , t
exp-eval-same true xm m p = refl , p
exp-eval-same false xm m p = refl , p
exp-eval-same (¬ b) xm m p with exp-eval-same b xm m p
... | q , r = cong not q , r
exp-eval-same (a₁ == a₂) xm m p with exp-eval-same a₁ xm m p
... | q , r with exp-eval-same a₂ (proj₂ (w⟦ a₁ ⟧ xm)) m r
...    | s , t rewrite q | s = refl , t
exp-eval-same (a₁ <= a₂) xm m p with exp-eval-same a₁ xm m p
... | q , r with exp-eval-same a₂ (proj₂ (w⟦ a₁ ⟧ xm)) m r
...    | s , t rewrite q | s = refl , t
exp-eval-same (b₁ :∨ b₂) xm m p with exp-eval-same b₁ xm m p
... | q , r with exp-eval-same b₂ (proj₂ (w⟦ b₁ ⟧ xm)) m r
...    | s , t = cong₂ _∨_ q s , t
exp-eval-same (b₁ :∧ b₂) xm m p  with exp-eval-same b₁ xm m p
... | q , r with exp-eval-same b₂ (proj₂ (w⟦ b₁ ⟧ xm)) m r
...    | s , t = cong₂ _∧_ q s , t

data _≋_ {n : ℕ} : XStmt n → Stmt n → Set where
  :=≋ : {x : Var n}{a : Exp n ℕ} →
    (x := a) ≋ (x := a)
  If≋ : {b : Exp n Bool}{s₁ s₂ : Stmt n} →
    (If b then s₁ else s₂) ≋ (If b then s₁ else s₂)
  While≋ : {b : Exp n Bool}{s : Stmt n} →
    (While b do s) ≋ (While b do s)
  Skip≋ : 
    Skip ≋ Skip
  Trans≋ : {s : Stmt n} → 
    (Trans s) ≋ (Trans s)
  ,,≋ : {xs : XStmt n} {s' s : Stmt n} → xs ≋ s' →
    (xs ,, s) ≋ (s' ,, s)
  ∥≋ : {xs₁ xs₂ : XStmt n} {s₁ s₂ : Stmt n} → xs₁ ≋ s₁ → xs₂ ≋ s₂ → 
    (xs₁ ∥ xs₂) ≋ (s₁ ∥ s₂)
  Intrans≋ : {xs : XStmt n}{wc rc : Cache n}{s : Stmt n} → 
    ((m : Mem n) → rc ≺ (m ◁) → ∃ λ (s' : Stmt n) → xs ≋ s' × ⟨ s / m ⟩ ⟶s* ⟨ s' / merge wc m ⟩) →
    (Intrans xs s wc rc) ≋ (Trans s)
  Trycommit≋ : {wc rc : Cache n}{s : Stmt n} → 
    ((m : Mem n) → rc ≺ (m ◁) → ⟨ s / m ⟩ ⟶s* ⟨ merge wc m ⟩) → 
    (Trycommit s wc rc) ≋ (Trans s)

data _∼_ {n h : ℕ} : XCfg n h → Cfg n → Set where
  Mem∼ : {xm : Stack n h}{m : Mem n} →
    xm ≈ m ◁ →
    ⟨ xm ⟩ ∼ ⟨ m ⟩
  Prog∼ : {xs : XStmt n}{s : Stmt n}{xm : Stack n h}{m : Mem n} →
    xs ≋ s → xm ≈ m ◁ →
    ⟨ xs / xm ⟩ ∼ ⟨ s / m ⟩

embsame : {n : ℕ}{s : Stmt n} → emb s ≋ s
embsame {_} {x := a}              = :=≋
embsame {_} {If b then s₁ else s₂} = If≋
embsame {_} {While b do s}        = While≋
embsame {_} {Skip}                = Skip≋
embsame {_} {Trans s}             = Trans≋
embsame {_} {s₁ ,, s₂}             = ,,≋ (embsame {_} {s₁})
embsame {_} {s₁ ∥ s₂}               = ∥≋ (embsame {_} {s₁}) (embsame {_} {s₂})

read∅≡ : {n h : ℕ} {xm : Stack n h} → (x : Var n) → read x (∅ ≪ ∅ ≪ xm) ≡ read x xm
read∅≡           zero = refl
read∅≡ {xm = xm} (suc x) rewrite sym (lemmapeel xm x) = read∅≡ x

stackmemlem : {n h : ℕ} {xm : Stack n h} → (wc : Cache n) → (rc : Cache n) → rc ≺ xm → (x : Var n) → read x (write wc (rcupdate rc xm)) ≡ read x (wc ≪ rc ≪ xm)
stackmemlem {zero} _ _ _ ()
stackmemlem {suc n} {zero} {(_ ∷ _) ◁} (just x ∷ xs) (_ ∷ _) _ zero = refl
stackmemlem {suc n} {suc h} {(_ ∷ _) ≪ (_ ∷ _) ≪ _} (just _ ∷ _) (_ ∷ _) _ zero = refl
stackmemlem {suc n} {zero} {(_ ∷ _) ◁} (nothing ∷ xs) (just x ∷ xs') p zero = sym (p zero refl)
stackmemlem {suc n} {suc h} {(just _ ∷ _) ≪ (_ ∷ _) ≪ _} (nothing ∷ xs) (just x ∷ xs') p zero = sym (p zero refl)
stackmemlem {suc n} {suc h} {(nothing ∷ _) ≪ (just _ ∷ _) ≪ _} (nothing ∷ xs) (just x ∷ xs') p zero = sym (p zero refl)
stackmemlem {suc n} {suc h} {(nothing ∷ _) ≪ (nothing ∷ _) ≪ _} (nothing ∷ xs) (just x ∷ xs') p zero = refl
stackmemlem {suc n} {zero} {(_ ∷ _) ◁} (nothing ∷ xs) (nothing ∷ xs') _ zero = refl
stackmemlem {suc n} {suc h} {(just _ ∷ _) ≪ (_ ∷ _) ≪ _} (nothing ∷ xs) (nothing ∷ xs') p zero = refl
stackmemlem {suc n} {suc h} {(nothing ∷ _) ≪ (just _ ∷ _) ≪ _} (nothing ∷ xs) (nothing ∷ xs') p zero = refl 
stackmemlem {suc n} {suc h} {(nothing ∷ _) ≪ (nothing ∷ _) ≪ _} (nothing ∷ xs) (nothing ∷ xs') p zero = refl
stackmemlem {suc n} {zero} {(_ ∷ xs) ◁} (_ ∷ wc) (_ ∷ rc) p (suc x) = stackmemlem {n} {zero} {xs ◁} wc rc (p ∘ suc) x
stackmemlem {suc n} {suc h} {(_ ∷ wc') ≪ (_ ∷ rc') ≪ xm} (_ ∷ wc) (_ ∷ rc) p (suc x) = stackmemlem {n} {suc h} {wc' ≪ rc' ≪ peel xm} wc rc (p ∘ suc) x


transcommit : {n h : ℕ} {xs : XStmt n} {s : Stmt n} {wc rc wc' rc' : Cache n} {xm : Stack n h} → ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶w* ⟨ wc' ≪ rc' ≪ xm ⟩ → ⟨ Intrans xs s wc rc / xm ⟩ ⟶w* ⟨ Trycommit s wc' rc' / xm ⟩
transcommit (Step y p) with p
transcommit (Step y p) | Finish = Step (Intrans⟶Fin y) Finish
transcommit (Step y p) | Step y' _ with stepcfg y y'
transcommit (Step y p) | Step _  _ | _ , _ ,  refl with stepsameh y
transcommit (Step y p) | Step _  _ | _ , ._ , refl | _ , _ , refl = Step (Intrans⟶Step y) (transcommit p)

mutual
  correct⟶s : {n h : ℕ} → 
           (c : Cfg n) → (c' : Cfg n) → (xc : XCfg n h) → c ⟶s c' → xc ∼ c → ∃ λ xc' → (xc ⟶w* xc') × (xc' ∼ c')
  correct⟶s ⟨ _ ⟩            _  _  ()                                     _
  correct⟶s ⟨ Skip / m ⟩     ._ ._ Skip⟶                                 (Prog∼ {._} {._} {xm} {._} Skip≋             r) = ⟨ xm ⟩ , Step Skip⟶ Finish , Mem∼ r
  correct⟶s ⟨ s₁ ,, s₂ / m ⟩ ._ ._ (,,⟶Fin {._} {._} {._} {m'} p)        (Prog∼ {._} {._} {xm} {._} (,,≋ {xs} {._} q) r) with correct⟶s ⟨ s₁ / m ⟩ ⟨ m' ⟩ ⟨ xs / xm ⟩ p (Prog∼ q r)
  ... | ⟨ xm' ⟩ , u , (Mem∼ t)= ⟨ emb s₂ / xm' ⟩ , Lazy.lem,,⟶Fin u , Prog∼ embsame t
  ... | ⟨ _ / _ ⟩ , _ , ()

  correct⟶s ⟨ s₁ ,, s₂ / m ⟩ ._ ._ (,,⟶Step {._} {._} {s₁'} {._} {m'} p) (Prog∼ {._} {._} {xm} {._} (,,≋ {xs} {._} q) r) with correct⟶s ⟨ s₁ / m ⟩ ⟨ s₁' / m' ⟩ ⟨ xs / xm ⟩ p (Prog∼ q r)
  ... | ⟨ _ ⟩ , _ , ()
  ... | ⟨ xs' / xm' ⟩ , u , (Prog∼ t v) = ⟨ xs' ,, s₂ / xm' ⟩ , Lazy.lem,,⟶Step u , Prog∼ (,,≋ t) v

  correct⟶s ⟨ s₁ ∥ s₂ / m ⟩ ._ ._ (∥⟶₁Fin {._} {._} {._} {m'} p)        (Prog∼ {._} {._} {xm} {._} (∥≋ {xs₁} {xs₂} {._} {._} q₁ q₂) r) with correct⟶s ⟨ s₁ / m ⟩ ⟨ m' ⟩ ⟨ xs₁ / xm ⟩ p (Prog∼ q₁ r)
  ... | ⟨ xm' ⟩ , u , (Mem∼ t) = ⟨ xs₂ / xm' ⟩ , Lazy.lem∥⟶₁Fin u , Prog∼ q₂ t
  ... | ⟨ _ / _ ⟩ , _ , ()

  correct⟶s ⟨ s₁ ∥ s₂ / m ⟩ ._ ._ (∥⟶₁Step {._} {s₁'} {._} {._} {m'} p) (Prog∼ {._} {._} {xm} {._} (∥≋ {xs₁} {xs₂} {._} {._} q₁ q₂) r) with correct⟶s ⟨ s₁ / m ⟩ ⟨ s₁' / m' ⟩ ⟨ xs₁ / xm ⟩ p (Prog∼ q₁ r)
  ... | ⟨ _ ⟩ , _ , ()
  ... | ⟨ xs₁' / xm' ⟩ , u , (Prog∼ v w) = ⟨ xs₁' ∥ xs₂ / xm' ⟩ , Lazy.lem∥⟶₁Step u , Prog∼ (∥≋ v q₂) w

  correct⟶s ⟨ s₁ ∥ s₂ / m ⟩ ._ ._ (∥⟶₂Fin {._} {._} {._} {m'} p)        (Prog∼ {._} {._} {xm} {._} (∥≋ {xs₁} {xs₂} {._} {._} q₁ q₂) r) with correct⟶s ⟨ s₂ / m ⟩ ⟨ m' ⟩ ⟨ xs₂ / xm ⟩ p (Prog∼ q₂ r)
  ... | ⟨ xm' ⟩ , u , (Mem∼ t) = ⟨ xs₁ / xm' ⟩ , Lazy.lem∥⟶₂Fin u , Prog∼ q₁ t
  ... | ⟨ _ / _ ⟩ , _ , ()

  correct⟶s ⟨ s₁ ∥ s₂ / m ⟩ ._ ._ (∥⟶₂Step {._} {._} {s₂'} {._} {m'} p) (Prog∼ {._} {._} {xm} {._} (∥≋ {xs₁} {xs₂} {._} {._} q₁ q₂) r) with correct⟶s ⟨ s₂ / m ⟩ ⟨ s₂' / m' ⟩ ⟨ xs₂ / xm ⟩ p (Prog∼ q₂ r)
  ... | ⟨ _ ⟩ , _ , ()
  ... | ⟨ xs₂' / xm' ⟩ , u , (Prog∼ v w) = ⟨ xs₁ ∥ xs₂' / xm' ⟩ , Lazy.lem∥⟶₂Step u , Prog∼ (∥≋ q₁ v) w

  correct⟶s ⟨ x := a / m ⟩  ._ ._ :=⟶                                    (Prog∼ {._} {._} {xm} {._} :=≋ r) = 
      ⟨ write (∅ [ x ]≔ just (proj₁ (w⟦ a ⟧ xm))) (proj₂ (w⟦ a ⟧ xm)) ⟩ , 
      Step :=⟶ Finish , 
      Mem∼ ((λ x' → subst (λ v → read x' (write (∅ [ x ]≔ just v) (proj₂ (w⟦ a ⟧ xm))) ≡ lookup x' (m [ x ]≔ s⟦ a ⟧ m)) (sym (proj₁ (exp-eval-same a xm m r))) (write-same-cons {xm = ⟦ a ⟧₂ xm} (proj₂ (exp-eval-same a xm m r)) x')))

  correct⟶s ⟨ If b then s₁ else s₂ / m ⟩ .(⟨ if s⟦ b ⟧ m then s₁ else s₂ / m ⟩) .(⟨ If b then s₁ else s₂ / xm ⟩) If⟶ (Prog∼ {.(If b then s₁ else s₂)} {.(If b then s₁ else s₂)} {xm} {.m} If≋ q) =
      ⟨ emb (if proj₁ (w⟦ b ⟧ xm) then s₁ else s₂) / proj₂ (w⟦ b ⟧ xm) ⟩ ,
      Step If⟶ Finish ,
      Prog∼ (subst (λ b' →  emb (if proj₁ (w⟦ b ⟧ xm) then s₁ else s₂) ≋ (if b' then s₁ else s₂)) (proj₁ (exp-eval-same b xm m q)) embsame) (proj₂ (exp-eval-same b xm m q))

  correct⟶s ⟨ While b do s / m ⟩ .(⟨ s ,, While b do s / m ⟩) .(⟨ While b do s / xm ⟩) (While⟶True p) (Prog∼ {._} {._} {xm} While≋ q) =
      ⟨ emb s ,, While b do s / proj₂ (w⟦ b ⟧ xm) ⟩ , 
      Step (While⟶True (subst (λ b → T b) (sym (proj₁ (exp-eval-same b xm m q))) p)) Finish ,
      Prog∼ embsame (proj₂ (exp-eval-same b xm m q))

  correct⟶s ⟨ While b do s / m ⟩ .(⟨ m ⟩) .(⟨ While b do s / xm ⟩) (While⟶False p) (Prog∼ {._} {._} {xm} While≋ q) =
      ⟨ proj₂ (w⟦ b ⟧ xm) ⟩ , 
      Step (While⟶False (subst (λ b → T (not b)) (sym (proj₁ (exp-eval-same b xm m q))) p)) Finish ,
      Mem∼ (proj₂ (exp-eval-same b xm m q))

  correct⟶s ⟨ Trans s / m ⟩ .(⟨ m' ⟩) .(⟨ Trans s / xm ⟩) (Trans⟶ {.s} {.m} {m'} p) (Prog∼ {._} {._} {xm} Trans≋ r) with correct⟶s* ⟨ s / m ⟩ ⟨ m' ⟩ ⟨ (emb s) / ∅ ≪ ∅ ≪ xm ⟩ p (Prog∼ embsame (λ x → trans (read∅≡ x) (r x)))
  ... | ⟨ _ / _ ⟩ , _ , ()
  ... | ⟨ wc ≪ rc ≪ xm₂ ⟩ , t , (Mem∼ u) with samefin t (consempty xm)
  ...    | w , o = ⟨ write wc (rcupdate rc xm) ⟩ , 
                   Step Trans⟶ (snoc (transcommit (subst (λ xm' → ⟨ emb s / ∅ ≪ ∅ ≪ xm ⟩ ⟶w* ⟨ wc ≪ rc ≪ xm' ⟩) (sym o) t)) (Commit xm (λ x {v} p → subst (λ xm → v ≡ read x xm) (sym o) (w x p)))) ,
                   Mem∼ (λ x → trans (subst (λ xm₂ → read x (write wc (rcupdate rc xm)) ≡ read x (wc ≪ rc ≪ xm₂)) o (stackmemlem wc rc (λ x {v} → subst (λ xm → lookup x rc ≡ just v → v ≡ read x xm) (sym o) (w x)) x)) (u x))

  correct⟶s ⟨ Trans s / m ⟩ .(⟨ m' ⟩) .(⟨ Intrans xs s twc trc / xm ⟩) (Trans⟶ {.s} {.m} {m'} p) (Prog∼ {.(Intrans xs s twc trc)} {.(Trans s)} {xm} {.m} (Intrans≋ {xs} {twc} {trc} {.s} q) r) with correct⟶s* ⟨ s / m ⟩ ⟨ m' ⟩ ⟨ (emb s) / ∅ ≪ ∅ ≪ xm ⟩ p (Prog∼ embsame (λ x → trans (read∅≡ x) (r x)))
  ... | ⟨ _ / _ ⟩ , _ , ()
  ... | ⟨ wc ≪ rc ≪ xm₂ ⟩ , t , (Mem∼ u) with samefin t (consempty xm)
  ...    | w , o = ⟨ write wc (rcupdate rc xm) ⟩ , 
                   Step Giveup (Step Trans⟶ (snoc (transcommit (subst (λ xm' → ⟨ emb s / ∅ ≪ ∅ ≪ xm ⟩ ⟶w* ⟨ wc ≪ rc ≪ xm' ⟩) (sym o) t)) (Commit xm (λ x {v} p → subst (λ xm → v ≡ read x xm) (sym o) (w x p))))) ,
                   Mem∼ (λ x → trans (subst (λ xm₂ → read x (write wc (rcupdate rc xm)) ≡ read x (wc ≪ rc ≪ xm₂)) o (stackmemlem wc rc (λ x {v} → subst (λ xm → lookup x rc ≡ just v → v ≡ read x xm) (sym o) (w x)) x)) (u x))

-- obvious solution, but Agda isn't convinced this will terminate so we'll do it the long way
-- with correct⟶s ⟨ Trans s / m ⟩ ⟨ m' ⟩ ⟨ Trans s / xm ⟩ (Trans⟶ p) (Prog∼ embsame r)
--  ... | a , b , c = a , Step Giveup b , c

  correct⟶s ⟨ Trans s / m ⟩ .(⟨ m' ⟩) .(⟨ Trycommit s twc trc / xm ⟩) (Trans⟶ {.s} {.m} {m'} p) (Prog∼ {.(Trycommit s twc trc)} {.(Trans s)} {xm} {.m} (Trycommit≋ {twc} {trc} {.s} q) r)  with correct⟶s* ⟨ s / m ⟩ ⟨ m' ⟩ ⟨ (emb s) / ∅ ≪ ∅ ≪ xm ⟩ p (Prog∼ embsame (λ x → trans (read∅≡ x) (r x)))
  ... | ⟨ _ / _ ⟩ , _ , ()
  ... | ⟨ wc ≪ rc ≪ xm₂ ⟩ , t , (Mem∼ u) with samefin t (consempty xm)
  ...    | w , o = ⟨ write wc (rcupdate rc xm) ⟩ , 
                   Step Abort (Step Trans⟶ (snoc (transcommit (subst (λ xm' → ⟨ emb s / ∅ ≪ ∅ ≪ xm ⟩ ⟶w* ⟨ wc ≪ rc ≪ xm' ⟩) (sym o) t)) (Commit xm (λ x {v} p → subst (λ xm → v ≡ read x xm) (sym o) (w x p))))) ,
                   Mem∼ (λ x → trans (subst (λ xm₂ → read x (write wc (rcupdate rc xm)) ≡ read x (wc ≪ rc ≪ xm₂)) o (stackmemlem wc rc (λ x {v} → subst (λ xm → lookup x rc ≡ just v → v ≡ read x xm) (sym o) (w x)) x)) (u x))

                               
  correct⟶s* : {n h : ℕ} → 
           (c : Cfg n) → (c' : Cfg n) → (xc : XCfg n h) → c ⟶s* c' → xc ∼ c → ∃ λ xc' → (xc ⟶w* xc') × (xc' ∼ c')
  correct⟶s* c .c xc Finish r = xc , Finish , r
  correct⟶s* c c'' xc (Step {.c}{c'}{.c''} p q) r with correct⟶s c c' xc p r
  ... | xc' , u , r' with correct⟶s* c' c'' xc' q r'
  ...    | xc'' , w , r'' = xc'' , Lazy.concat* u w , r''

read-flatten : {n : ℕ}{wc rc : Cache n}{h : ℕ}{xm : Stack n h}{m : Mem n} → 
  xm ≈ m ◁ → rc ≺ (m ◁) → (x : Fin n) → read x (wc ≪ rc ≪ xm) ≡ lookup x (merge wc m)
read-flatten {zero} _ _ () 
read-flatten {suc n} {just _ ∷ _}  {_ ∷ _}       {_} {_}  {_ ∷ _} _ _ zero    = refl
read-flatten {suc n} {nothing ∷ _} {just _ ∷ _}  {_} {_}  {_ ∷ _} _ q zero    = q zero refl
read-flatten {suc n} {nothing ∷ _} {nothing ∷ _} {_} {_}  {_ ∷ _} p _ zero    = p zero
read-flatten {suc n} {_ ∷ wc}      {_ ∷ rc}      {_} {xm} {_ ∷ _} p q (suc x) = read-flatten (λ x → trans (lemmapeel xm x) (p (suc x))) (q ∘ suc) x


read-same : {n : ℕ} → (x : Var n) → (m : Mem n) → read x (m ◁) ≡ lookup x m
read-same {zero}  ()      _
read-same {suc _} zero    (_ ∷ _) = refl
read-same {suc _} (suc x) (_ ∷ m) = read-same x m

mc : {n : ℕ} {wc : Cache n} {m : Mem n} → (x : Var n) → {v : ℕ} → merge wc m [ x ]≔ v ≡ merge (wcmerge (∅ [ x ]≔ just v) wc) m
mc {zero} ()
mc {suc _} {_ ∷ wc}       {_ ∷ m} zero    {v} = cong (λ c → v ∷ merge c m) (sym (wcmerge≡ wc))
mc {suc _} {just v ∷ wc}  {_ ∷ m} (suc x) {_} = cong (λ m → v ∷ m) (mc x)
mc {suc _} {nothing ∷ wc} {v ∷ m} (suc x) {_} = cong (λ m → v ∷ m) (mc x)

mt : {n : ℕ}{c₁ c₂ : Cache n}{m : Mem n} → merge c₁ (merge c₂ m) ≡ merge (wcmerge c₁ c₂) m
mt {zero} {[]} {[]} {[]} = refl
mt {suc n} {nothing ∷ c₁} {nothing ∷ c₂} {v ∷ m} = cong (λ m → v ∷ m) mt
mt {suc n} {nothing ∷ c₁} {just v ∷ c₂}  {_ ∷ m} = cong (λ m → v ∷ m) mt
mt {suc n} {just v ∷ c₁}  {_ ∷ c₂}       {_ ∷ m} = cong (λ m → v ∷ m) mt

rcm : {n : ℕ} {rc0 wc rc : Cache n} {m : Mem n} {h : ℕ} {xm : Stack n h} → rcmerge rc0 wc rc ≺ (m ◁) → rc0 ≺ (wc ≪ rc ≪ xm) → rc0 ≺ (merge wc m ◁)
rcm {zero}                                          _ _ () _
rcm {suc _} {nothing ∷ _} {wv ∷ _}      {rv ∷ _}      p q zero ()
rcm {suc _} {just _ ∷ _}  {nothing ∷ _} {nothing ∷ _} {_ ∷ _} p q zero refl = p zero refl
rcm {suc _} {just _ ∷ _}  {nothing ∷ _} {just _ ∷ _}  {_ ∷ _} p q zero refl = trans (q zero refl) (p zero refl)
rcm {suc _} {just _ ∷ _}  {just _ ∷ _}  {rv ∷ _}      {_ ∷ _} p q zero refl = q zero refl
rcm {suc _} {_ ∷ rc0} {_ ∷ wc} {_ ∷ rc} {_ ∷ m} p q (suc x) r = rcm (p ∘ suc) (q ∘ suc) x r

bar : {n h : ℕ}{wc rc : Cache n}{xm : Stack n h}{rc' : Cache n}{m : Mem n}{A : Set} → (e : Exp n A) →
  ⟦ e ⟧₂ (wc ≪ rc ≪ xm) ≡ wc ≪ rc' ≪ xm → rc' ≺ (m ◁) → ⟦ e ⟧₁ (wc ≪ rc ≪ xm) ≡ s⟦ e ⟧ (merge wc m)
bar {zero} (V ()) _ _
bar {wc = nothing ∷ _} {nothing ∷ _} {m = _ ∷ _} (V zero)    refl q = q zero refl
bar {wc = nothing ∷ _} {just _ ∷ _}  {m = _ ∷ _} (V zero)    refl q = q zero refl
bar {wc = just _ ∷ _}  {rv ∷ _}      {m = _ ∷ _} (V zero)    refl _ = refl
bar {wc = wv ∷ _}      {_ ∷ _}       {m = _ ∷ _} (V (suc x)) refl q = bar (V x) refl (q ∘ suc)
bar (N y) refl q = refl
bar {wc = wc} {rc} {xm = xm} (e₁ :+ e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r
                     | bar e₂ p q
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl
bar {wc = wc} {rc} {xm = xm} (e₁ :- e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r
                     | bar e₂ p q
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl
bar {wc = wc} {rc} {xm = xm} (e₁ :× e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r
                     | bar e₂ p q
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl
bar true refl _ = refl
bar false refl _ = refl
bar (¬ y) p q = cong not (bar y p q)
bar {wc = wc} {rc} {xm = xm} (e₁ == e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r 
                     | bar e₂ p q 
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl
bar {wc = wc} {rc} {xm = xm} (e₁ <= e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r
                     | bar e₂ p q
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl
bar {wc = wc} {rc} {xm = xm} (e₁ :∨ e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r
                     | bar e₂ p q
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl
bar {wc = wc} {rc} {xm = xm} (e₁ :∧ e₂) p q with lem0 wc rc xm e₁
... | rc'' , r rewrite r
                     | bar e₂ p q
                     | bar e₁ r (λ x t → q x (expinvar-rc e₂ xm p x t)) = refl


foo' : {n h : ℕ}{xm : Stack n h}{m : Mem n}{wc rc wc' rc' : Cache n}{xm' : Stack n (suc h)}{xs : XStmt n}{s : Stmt n} →
    ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶w ⟨ xm' ⟩ → xm' ≡ wc' ≪ rc' ≪ xm → xs ≋ s → rc' ≺ (m ◁) →
    ⟨ s / merge wc m ⟩ ⟶s* ⟨ merge wc' m ⟩

foo' Skip⟶ refl Skip≋ _ = Step Skip⟶ Finish

foo' (While⟶False y) p (While≋ {b} {s}) r with expinvar-wc _ b p
... | refl = Step (While⟶False (subst (λ v → T (not v)) (bar b p r) y)) Finish

foo' {_} {_} {xm} {_} {wc} {rc}             :=⟶ _ (:=≋ {_} {a}) _ with lem0 wc rc xm a
foo' {_} {_} {xm} {_} {wc} {rc} {wc'} {rc'} :=⟶ p (:=≋ {x} {a}) _ | _  , w with subst (λ m → write (∅ [ x ]≔ just (⟦ a ⟧₁ (wc ≪ rc ≪ xm))) m ≡ wc' ≪ rc' ≪ xm) w p
foo' {_} {_} {xm} {m} {wc} {rc}             :=⟶ p (:=≋ {x} {a}) q | ._ , w | refl = Step (subst (λ m' → ⟨ x := a / merge wc m ⟩ ⟶s ⟨ m' ⟩) (subst (λ v → merge wc m [ x ]≔ s⟦ a ⟧ (merge wc m) ≡ merge (wcmerge (∅ [ x ]≔ just v) wc) m) (sym (bar a w q)) (mc x)) :=⟶) Finish

foo' {_} {_} {xm} {m} {wc} {rc} (Commit ._ y) refl (Trycommit≋ {wc0} {rc0} {s} q) r = Step (Trans⟶ (subst (λ m' → ⟨ s / merge wc m ⟩ ⟶s* ⟨ m' ⟩) mt (q (merge wc m) (rcm r y)))) Finish


foo : {n : ℕ}{s : Stmt n}{m : Mem n}{wc rc wc' rc' : Cache n}{xs xs' : XStmt n}{h : ℕ}{xm : Stack n h}{xm' : Stack n (suc h)} →
  ⟨ xs / wc ≪ rc ≪ xm ⟩ ⟶w ⟨ xs' / xm' ⟩ → xm' ≡ wc' ≪ rc' ≪ xm → xs ≋ s → rc' ≺ (m ◁) →
  ∃ λ s' → ⟨ s / merge wc m ⟩ ⟶s* ⟨ s' / merge wc' m ⟩ × xs' ≋ s'
foo (,,⟶Fin y) p (,,≋ q) r = _ , Strong.lem,,⟶Fin (foo' y p q r) , embsame
foo (,,⟶Step y) p (,,≋ q) r with foo y p q r
... | _ , steps , t = _ , Strong.lem,,⟶Step steps , ,,≋ t
foo (∥⟶₁Fin y) p (∥≋ q₁ q₂) r = _ , Strong.lem∥⟶₁Fin (foo' y p q₁ r) , q₂
foo (∥⟶₁Step y) p (∥≋ q₁ q₂) r with foo y p q₁ r
... | _ , steps , t = _ , Strong.lem∥⟶₁Step steps , ∥≋ t q₂
foo (∥⟶₂Fin y) p (∥≋ q₁ q₂) r = _ , Strong.lem∥⟶₂Fin (foo' y p q₂ r) , q₁
foo (∥⟶₂Step y) p (∥≋ q₁ q₂) r with foo y p q₂ r
... | _ , steps , t = _ , Strong.lem∥⟶₂Step steps , ∥≋ q₁ t

foo {_} {._} {m} {wc} If⟶ p (If≋ {b} {s₁} {s₂}) r with expinvar-wc _ b p
... | refl = _ , Step (subst (λ v → ⟨ If b then s₁ else s₂ / merge wc m ⟩ ⟶s ⟨ if v then s₁ else s₂ / merge wc m ⟩) (sym (bar b p r)) If⟶) Finish , embsame

foo (While⟶True y) p (While≋ {b} {s}) r with expinvar-wc _ b p
... | refl = _ , Step (While⟶True (subst T (bar b p r) y)) Finish , ,,≋ embsame

foo Trans⟶ refl (Trans≋ {s}) r = _ , Finish , Intrans≋ (λ m p → _ , embsame , subst (λ m' → ⟨ s / m ⟩ ⟶s* ⟨ s / m' ⟩) (sym (merge≡ m)) Finish)

foo (Intrans⟶Step {._} {xs'} {._} {._} {._} {wc'} {rc'} p) refl (Intrans≋ {xs} {wc} {rc} {s} q) r = _ , Finish , Intrans≋ f
    where f : (m' : Vec ℕ _) → rc' ≺ (m' ◁) → ∃ λ s' → xs' ≋ s' × ⟨ s / m' ⟩ ⟶s* ⟨ s' / merge wc' m' ⟩
          f m' s with q m' (rcStep {xm' = m' ◁} p s)
          ... | s' , o , u with foo p refl o s
          ...    | s'' , w , x = s'' , x , Strong.concat* u w 
foo (Intrans⟶Fin {._} {._} {._} {._} {wc'} {rc'} p) refl (Intrans≋ {xs} {wc} {rc} {s} q) r = _ , Finish , Trycommit≋ f
    where f : (m' : Vec ℕ _) → rc' ≺ (m' ◁) → ⟨ s / m' ⟩ ⟶s* ⟨ merge wc' m' ⟩
          f m' s with q m' (rcFin {xm' = m' ◁} p s)
          ... | s' , o , u = Strong.concat* u (foo' p refl o s)
foo Abort refl (Trycommit≋ _) _ = _ , Finish , Trans≋
foo Giveup refl (Intrans≋ _) _ = _ , Finish , Trans≋


correct⟶w : {n h : ℕ} → 
           (xc : XCfg n h) → (xc' : XCfg n h) → (c : Cfg n) →    xc ⟶w xc' →  xc ∼ c    → ∃ λ c' → (c ⟶s* c') × (xc' ∼ c')

correct⟶w ⟨ Skip / xm ⟩    .(⟨ xm ⟩)           .(⟨ Skip / m ⟩)    Skip⟶                           (Prog∼ {._} {._} {._} {m} Skip≋ p) =  
    ⟨ m ⟩ , 
    Step Skip⟶ Finish , 
    Mem∼ p

correct⟶w ⟨ xs ,, s / xm ⟩ .(⟨ emb s / xm' ⟩)  .(⟨ s₁ ,, s / m ⟩) (,,⟶Fin {._} {._} {._} {xm'} p) (Prog∼ {._} {._} {._} {m} (,,≋ {._} {s₁} {._} q) r) with correct⟶w ⟨ xs / xm ⟩ ⟨ xm' ⟩ ⟨ s₁ / m ⟩ p (Prog∼ q r)
... | ⟨ m' ⟩    , u , (Mem∼ t) = ⟨ s / m' ⟩ , Strong.lem,,⟶Fin u , (Prog∼ embsame t)
... | ⟨ _ / _ ⟩ , _ , ()
  
correct⟶w ⟨ xs ,, s / xm ⟩ .(⟨ xs' ,, s / xm' ⟩) .(⟨ s₁ ,, s / m ⟩) (,,⟶Step {.xs} {xs'} {.s} {.xm} {xm'} p) (Prog∼ {.(xs ,, s)} {.(s₁ ,, s)} {.xm} {m} (,,≋ {.xs} {s₁} {.s} q) r) with  correct⟶w ⟨ xs / xm ⟩ ⟨ xs' / xm' ⟩ ⟨ s₁ / m ⟩ p (Prog∼ q r)
... | ⟨ _ ⟩ , _ , ()
... | ⟨ s₁' / m' ⟩ , u , (Prog∼ v w) = ⟨ s₁' ,, s / m' ⟩ , Strong.lem,,⟶Step u , Prog∼ (,,≋ v) w

correct⟶w ⟨ xs₁ ∥ xs₂ / xm ⟩ .(⟨ xs₂ / xm' ⟩) .(⟨ s₁ ∥ s₂ / m ⟩) (∥⟶₁Fin {.xs₁} {.xs₂} {.xm} {xm'} p)  (Prog∼ {.(xs₁ ∥ xs₂)} {.(s₁ ∥ s₂)} {.xm} {m} (∥≋ {.xs₁} {.xs₂} {s₁} {s₂} q₁ q₂) r) with correct⟶w ⟨ xs₁ / xm ⟩ ⟨ xm' ⟩ ⟨ s₁ / m ⟩ p (Prog∼ q₁ r)
... | ⟨ m' ⟩ , u , (Mem∼ t) = ⟨ s₂ / m' ⟩ , Strong.lem∥⟶₁Fin u , Prog∼ q₂ t
... | ⟨ _ / _ ⟩ , _ , ()

correct⟶w ⟨ xs₁ ∥ xs₂ / xm ⟩ .(⟨ xs₁ / xm' ⟩) .(⟨ s₁ ∥ s₂ / m ⟩) (∥⟶₂Fin {.xs₁} {.xs₂} {.xm} {xm'} p) (Prog∼ {.(xs₁ ∥ xs₂)} {.(s₁ ∥ s₂)} {.xm} {m} (∥≋ {.xs₁} {.xs₂} {s₁} {s₂} q₁ q₂) r) with correct⟶w ⟨ xs₂ / xm ⟩ ⟨ xm' ⟩ ⟨ s₂ / m ⟩ p (Prog∼ q₂ r)
... | ⟨ m' ⟩ , u , (Mem∼ t) = ⟨ s₁ / m' ⟩ , Strong.lem∥⟶₂Fin u , Prog∼ q₁ t
... | ⟨ _ / _ ⟩ , _ , ()

correct⟶w ⟨ xs₁ ∥ xs₂ / xm ⟩ .(⟨ xs₁' ∥ xs₂ / xm' ⟩) .(⟨ s₁ ∥ s₂ / m ⟩) (∥⟶₁Step {.xs₁} {xs₁'} {.xs₂} {.xm} {xm'} p)  (Prog∼ {.(xs₁ ∥ xs₂)} {.(s₁ ∥ s₂)} {.xm} {m} (∥≋ {.xs₁} {.xs₂} {s₁} {s₂} q₁ q₂) r) with correct⟶w ⟨ xs₁ / xm ⟩ ⟨ xs₁' / xm' ⟩ ⟨ s₁ / m ⟩ p (Prog∼ q₁ r)
... | ⟨ _ ⟩ , _ , ()
... | ⟨ s₁' / m' ⟩ , u , (Prog∼ q₁' r') = ⟨ s₁' ∥ s₂ / m' ⟩ , Strong.lem∥⟶₁Step u , Prog∼ (∥≋ q₁' q₂) r'

correct⟶w ⟨ xs₁ ∥ xs₂ / xm ⟩ .(⟨ xs₁ ∥ xs₂' / xm' ⟩) .(⟨ s₁ ∥ s₂ / m ⟩) (∥⟶₂Step {.xs₁} {.xs₂} {xs₂'} {.xm} {xm'} p)  (Prog∼  {.(xs₁ ∥ xs₂)} {.(s₁ ∥ s₂)} {.xm} {m} (∥≋ {.xs₁} {.xs₂} {s₁} {s₂} q₁ q₂) r) with correct⟶w ⟨ xs₂ / xm ⟩ ⟨ xs₂' / xm' ⟩ ⟨ s₂ / m ⟩ p (Prog∼ q₂ r)
... | ⟨ _ ⟩ , _ , ()
... | ⟨ s₂' / m' ⟩ , u , (Prog∼ q₂' r') = ⟨ s₁ ∥ s₂' / m' ⟩ , Strong.lem∥⟶₂Step u , Prog∼ (∥≋ q₁ q₂') r'

correct⟶w ⟨ x := a / xm ⟩ .(⟨ write (∅ [ x ]≔ just (proj₁ (w⟦ a ⟧ xm))) (proj₂ (w⟦ a ⟧ xm)) ⟩) .(⟨ x := a / m ⟩) :=⟶ (Prog∼ {._} {._} {._} {m} :=≋ r) with exp-eval-same a xm m r 
... | p , q =
    ⟨ m [ x ]≔ s⟦ a ⟧ m ⟩ , 
    Step :=⟶ Finish , 
    Mem∼ (λ x' → subst (λ v → read x' (write (∅ [ x ]≔ just v) (⟦ a ⟧₂ xm)) ≡ lookup x' (m [ x ]≔ s⟦ a ⟧ m)) (sym p) (write-same-cons {xm = ⟦ a ⟧₂ xm} q x'))

correct⟶w ⟨ If b then s₁ else s₂ / xm ⟩ .(⟨ emb (if proj₁ (w⟦ b ⟧ xm) then s₁ else s₂) / proj₂ (w⟦ b ⟧ xm) ⟩) .(⟨ If b then s₁ else s₂ / m ⟩) If⟶ (Prog∼ {._} {._} {._} {m} If≋ q) = 
    ⟨ if s⟦ b ⟧ m then s₁ else s₂ / m ⟩ , 
    Step If⟶ Finish , 
    (Prog∼ ((subst (λ b' → emb (if proj₁ (w⟦ b ⟧ xm) then s₁ else s₂) ≋ (if b' then s₁ else s₂)) 
              (proj₁ (exp-eval-same b xm m q)) 
              embsame)) 
             (proj₂ (exp-eval-same b xm m q))) 

correct⟶w ⟨ While b do s / xm ⟩ .(⟨ emb s ,, While b do s / proj₂ (w⟦ b ⟧ xm) ⟩) .(⟨ While b do s / m ⟩) (While⟶True p) (Prog∼ {._} {._} {.xm} {m} While≋ q) = 
    ⟨ s ,, While b do s / m ⟩ , 
    Step (While⟶True (subst (λ b → T b) (proj₁ (exp-eval-same b xm m q)) p)) Finish , 
    Prog∼ embsame (proj₂ (exp-eval-same b xm m q))

correct⟶w ⟨ While b do s / xm ⟩ .(⟨ proj₂ (w⟦ b ⟧ xm) ⟩) .(⟨ While b do s / m ⟩) (While⟶False p) (Prog∼ {._} {._} {.xm} {m} While≋ q) =
    ⟨ m ⟩ ,
    Step (While⟶False (subst (λ b → T (not b)) (proj₁ (exp-eval-same b xm m q)) p)) Finish ,
    Mem∼ (proj₂ (exp-eval-same b xm m q))

correct⟶w ⟨ Trans s / xm ⟩ .(⟨ Intrans (emb s) s ∅ ∅ / xm ⟩) .(⟨ Trans s / m ⟩) Trans⟶ (Prog∼ {.(Trans s)} {.(Trans s)} {.xm} {m} Trans≋ q) = 
    ⟨ Trans s / m ⟩ , Finish , Prog∼ (Intrans≋ (λ m p → s , embsame , subst (λ m' → ⟨ s / m ⟩ ⟶s* ⟨ s / m' ⟩) (sym (merge≡ m)) Finish)) q

correct⟶w ⟨ Trycommit s wc rc / xm ⟩ .(⟨ Trans s / xm ⟩) .(⟨ Trans s / m ⟩) Abort (Prog∼ {.(Trycommit s wc rc)} {.(Trans s)} {.xm} {m} (Trycommit≋ _) q) = 
    ⟨ Trans s / m ⟩ , Finish , Prog∼ Trans≋ q

correct⟶w ⟨ Intrans xs s wc rc / xm ⟩ .(⟨ Trans s / xm ⟩) .(⟨ Trans s / m ⟩) Giveup (Prog∼ {.(Intrans xs s wc rc)} {.(Trans s)} {.xm} {m} (Intrans≋ _) q) =
    ⟨ Trans s / m ⟩ , Finish , Prog∼ Trans≋ q

correct⟶w ⟨ Intrans xs s wc rc / xm ⟩ .(⟨ Intrans xs' s wc' rc' / xm ⟩) .(⟨ Trans s / m ⟩) (Intrans⟶Step {.xs} {xs'} {.s} {.wc} {.rc} {wc'} {rc'} {.xm} p) (Prog∼ {.(Intrans xs s wc rc)} {.(Trans s)} {.xm} {m} (Intrans≋ r) q) = 
   ⟨ Trans s / m ⟩ , Finish , Prog∼ (Intrans≋ f) q
     where f : (m' : Vec ℕ _) → rc' ≺ (m' ◁) → ∃ λ s' → xs' ≋ s' × ⟨ s / m' ⟩ ⟶s* ⟨ s' / merge wc' m' ⟩
           f m' t with r m' (rcStep {xm' = m' ◁} p t) 
           ... | s' , v , w with foo p refl v t
           ...    | s'' , u , o = s'' , o , Strong.concat* w u

correct⟶w ⟨ Intrans xs s wc rc / xm ⟩ .(⟨ Trycommit s wc' rc' / xm ⟩) .(⟨ Trans s / m ⟩) (Intrans⟶Fin {.xs} {.s} {.wc} {.rc} {wc'} {rc'} {.xm} p) (Prog∼ {.(Intrans xs s wc rc)} {.(Trans s)} {.xm} {m} (Intrans≋ a) q) = 
    ⟨ Trans s / m ⟩ , 
    Finish , 
    Prog∼ (Trycommit≋ f) q
     where f : (m' : Vec ℕ _) → rc' ≺ (m' ◁) → ⟨ s / m' ⟩ ⟶s* ⟨ merge wc' m' ⟩
           f m' t  with a m' (rcFin {xm' = m' ◁} p t)
           ... | s' , v , w = Strong.concat* w (foo' p refl v t)


correct⟶w ⟨ Trycommit s wc rc / xm ⟩ .(⟨ write wc (rcupdate rc xm) ⟩) .(⟨ Trans s / m ⟩) (Commit ._ p) (Prog∼ {._} {._} {._} {m} (Trycommit≋ a) q) = 
    ⟨ merge wc m ⟩ , Step (Trans⟶ (a m (λ x r → trans (p x r) (trans (q x) (sym (read-same x m)))))) Finish , Mem∼ (λ x → trans (stackmemlem {xm = xm} wc rc p x) (read-flatten q (λ x r →  trans (p x r) (trans (q x) (sym (read-same x m)))) x))

correct⟶w ⟨ _ ⟩ _   _  () _


correct⟶w* :  {n h : ℕ} → (xc : XCfg n h) → (xc' : XCfg n h) → (c : Cfg n) → xc ⟶w* xc' → xc ∼ c → ∃ λ c' → (c ⟶s* c') × (xc' ∼ c')
correct⟶w* xc .xc c Finish r = c , Finish , r
correct⟶w* xc xc'' c (Step {.xc}{xc'}{.xc''} p q) r with correct⟶w xc xc' c p r
... | c' , u , r' with correct⟶w* xc' xc'' c' q r'
...     | c'' , w , r'' = c'' , Strong.concat* u w , r''
