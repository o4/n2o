module Infinity.Inductive.Empty where

open import Infinity.Proto using (ℓ)

data ⊥ : Set where

efq : ∀ {A : Set ℓ} → ⊥ → A
efq ()

infix 3 ¬_

¬_ : Set ℓ → Set ℓ
¬ P = P → ⊥

