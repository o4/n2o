{-# OPTIONS --cubical --safe #-}

module Infinity.Equiv where

open import Infinity.Path
open import Infinity.Sigma 

open import Agda.Builtin.Cubical.Glue using (isEquiv ; _≃_)

open isEquiv public

isPropIsEquiv' : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv' f u0 u1 i) y = isPropIsContr (u0 .equiv-proof y) (u1 .equiv-proof y) i

isPropIsEquiv : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv f p q i) y =
  let p2 = p .equiv-proof y .π⃑
      q2 = q .equiv-proof y .π⃑
   in p2 (q .equiv-proof y .π⃐) i , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                                                           ; (i = i1) → q2 w (j ∨ ~ k)
                                                           ; (j = i0) → p2 (q2 w (~ k)) i
                                                           ; (j = i1) → w }) (p2 w (i ∨ j))

module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where

  propPi : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
  propPi h f0 f1 i x = h x (f0 x) (f1 x) i

  isProp→PathP : ((x : A) → isProp (B x)) → {a0 a1 : A} (p : a0 ≡ a1) (b0 : B a0) (b1 : B a1) → PathP (λ i → B (p i)) b0 b1
  isProp→PathP P p b0 b1 i = P (p i) (transp (λ j → B (p (i ∧ j))) (~ i) b0) (transp (λ j → B (p (i ∨ ~ j))) i b1) i

equivEq : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (e f : A ≃ B) → (h : e .π⃐ ≡ f .π⃐) → e ≡ f
equivEq e f h = λ i → (h i) , isProp→PathP isPropIsEquiv h (e .π⃑) (f .π⃑) i

module _ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g : B → A)
         (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) where

  private

    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where

      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k; (i = i0) → g y }) (inc (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k; (i = i0) → g y }) (inc (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1; (i = i0) → fill0 k i1 }) (inc (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y }) (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k }) (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .π⃐ = p i
      lemIso i .π⃑ = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .π⃐ .π⃐ = g y
  isoToIsEquiv .equiv-proof y .π⃐ .π⃑ = s y
  isoToIsEquiv .equiv-proof y .π⃑ z = lemIso y (g y) (π⃐ z) (s y) (π⃑ z)

  isoToEquiv : A ≃ B
  isoToEquiv = _ , isoToIsEquiv

module _ {A : Set ℓ₁} {B : Set ℓ₂} (w : A ≃ B) where

  invEq : B → A
  invEq y = π⃐ (π⃐ (π⃑ w .equiv-proof y))

  secEq : (x : A) → invEq (π⃐ w x) ≡ x
  secEq x = λ i → π⃐ (π⃑ (π⃑ w .equiv-proof (π⃐ w x)) (x , (λ j → π⃐ w x)) i)

  retEq : (y : B) → π⃐ w (invEq y) ≡ y
  retEq y = λ i → π⃑ (π⃐ (π⃑ w .equiv-proof y)) i

invEquiv : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → A ≃ B → B ≃ A
invEquiv f = isoToEquiv (invEq f) (π⃐ f) (secEq f) (retEq f)

compEquiv : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → A ≃ B → B ≃ C → A ≃ C
compEquiv f g = isoToEquiv (λ x → g .π⃐ (f .π⃐ x))
                           (λ x → invEq f (invEq g x))
                           (λ y → compPath (cong (g .π⃐) (retEq f (invEq g y))) (retEq g y))
                           (λ y → compPath (cong (invEq f) (secEq g (f .π⃐ y))) (secEq f y))

