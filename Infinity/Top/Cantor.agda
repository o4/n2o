{-# OPTIONS --cubical --safe #-}

module Infinity.Top.Cantor where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.Inductive.Two

Cantor : Set 
Cantor = ℕ → 𝟚

decreasing : Cantor → Set 
decreasing f = (i : ℕ) → f i ≥ f (succ i)

ℕ∞ : Set 
ℕ∞ = ∃ λ (a : Cantor) → decreasing a

-- ∞ : ℕ∞
-- ∞ = (λ _ → 𝟙) , λ _ → {!!} (𝟙 ≡ 𝟙)

