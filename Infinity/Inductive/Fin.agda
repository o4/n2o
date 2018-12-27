module Infinity.Inductive.Fin where

open import Infinity.Proto

variable n : ℕ

data Fin : ℕ → Set where
  fz : Fin (succ n)
  fs : (i : Fin n) → Fin (succ n)

toℕ : Fin n → ℕ
toℕ fz     = zero
toℕ (fs i) = succ (toℕ i)

fromℕ : (n : ℕ) → Fin (succ n)
fromℕ zero    = fz
fromℕ (succ n) = fs (fromℕ n)
