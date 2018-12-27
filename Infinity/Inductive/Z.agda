{-# OPTIONS --cubical --safe #-}

module Infinity.Inductive.Z where

open import Infinity.Proto
open import Infinity.Path
open import Infinity.Equiv
open import Infinity.Univ

data ℤ : Set where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

ℤtoℕ : ℤ → ℕ
ℤtoℕ (pos    n) = n 
ℤtoℕ (negsuc n) = n

ℕtoℤ : ℕ → ℤ 
ℕtoℤ zero     = pos zero
ℕtoℤ (succ n) = pos n

sucℤ : ℤ → ℤ
sucℤ (pos n)           = pos (succ n)
sucℤ (negsuc zero)     = pos zero
sucℤ (negsuc (succ n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero)       = negsuc zero
predℤ (pos (succ n))   = pos n
predℤ (negsuc n)       = negsuc (succ n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)        = refl
sucPred (pos (succ n))    = refl
sucPred (negsuc zero)     = refl
sucPred (negsuc (succ n)) = refl

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos zero)        = refl
predSuc (pos (succ n))    = refl
predSuc (negsuc zero)     = refl
predSuc (negsuc (succ n)) = refl

oneℤ : ℤ 
oneℤ = pos (succ zero)

twoℤ : ℤ
twoℤ = pos (succ (succ zero))

suc-equiv : ℤ ≃ ℤ
suc-equiv .π⃐ = sucℤ
suc-equiv .π⃑ = isoToIsEquiv sucℤ predℤ sucPred predSuc

sucPathInt : ℤ ≡ ℤ
sucPathInt = ua suc-equiv
