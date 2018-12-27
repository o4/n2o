{-# OPTIONS --cubical --safe #-}

module Infinity.Sigma where

open import Agda.Builtin.Sigma public renaming (fst to π⃐; snd to π⃑)

open import Infinity.Proto
open import Infinity.Inductive.Empty

Σ-map : ∀ {A : Set ℓ} {B C : A → Set ℓ} → ((a : A) → B a → C a) → Σ A B → Σ A C
Σ-map f (a , b) = (a , f a b)

Σ-ind : ∀ {S : Set ℓ₁} {T : S → Set ℓ₁} { P : Σ S T → Set ℓ₂} → ((s : S)(t : T s) → P (s , t)) → (p : Σ S T) → P p
(Σ-ind p) (s , t) = p s t

∃ : ∀ {A : Set ℓ₁} → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
∃ = Σ _

∄ : ∀ {A : Set ℓ₁} → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
∄ P = ¬ ∃ P

infix 2 Σ-syntax

Σ-syntax : (A : Set ℓ₁) (B : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixl 40 _×_

_×_ : (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ[ _ ∈ A ] B

uncurry : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (x : A) → B x → Set ℓ₃} → (∀ x y → C x y) → (∀ s → C (π⃐ s) (π⃑ s))
uncurry f (x , y) = f x y

