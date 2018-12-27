{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.Trunc where

open import Infinity.Proto
open import Infinity.Path

data ∥_∥ (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

recPropTrunc : ∀ {A : Set ℓ} {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
recPropTrunc Pprop f ∣ x ∣ = f x
recPropTrunc Pprop f (squash x y i) = Pprop (recPropTrunc Pprop f x) (recPropTrunc Pprop f y) i

propTruncIsProp : ∀ {A : Set ℓ} → isProp ∥ A ∥
propTruncIsProp x y = squash x y

elimPropTrunc : ∀ {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc Pprop f ∣ x ∣ = f x
elimPropTrunc {A = A} {P = P} Pprop f (squash x y i) =
  PpropOver (squash x y) (elimPropTrunc Pprop f x) (elimPropTrunc Pprop f y) i where
  PpropOver : {a b : ∥ A ∥} → (sq : a ≡ b) → ∀ x y → PathP (λ i → P (sq i)) x y
  PpropOver {a} = J (λ b (sq : a ≡ b) → ∀ x y → PathP (λ i → P (sq i)) x y) (Pprop a)

-- We could also define the eliminator using the recursor
elimPropTrunc' : ∀ {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
elimPropTrunc' {P = P} Pprop f a = recPropTrunc (Pprop a) (λ x → transp (λ i → P (squash ∣ x ∣ a i)) i0 (f x)) a

