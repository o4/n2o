module Infinity.Inductive.Either where

open import Infinity.Proto

data _⊎_ (A B : Set ℓ) : Set ℓ where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

either : ∀ {A B C : Set ℓ} → (A → C) → (B → C) → A ⊎ B → C
either f g (inl x) = f x
either f g (inr x) = g x

