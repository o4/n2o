{-# OPTIONS --cubical #-}

module Infinity.HIT.Interval where

open import Infinity.Core
open import Infinity.Proto
open import Infinity.Path

data Interval : Set where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

funExtInterval : (A B : Set ℓ) (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
funExtInterval A B f g p = λ i x → hmtpy x (seg i)
  where
  hmtpy : A → Interval → B
  hmtpy x zero    = f x
  hmtpy x one     = g x
  hmtpy x (seg i) = p x i

intervalElim : ∀ {A : Set ℓ} (x y : A) (p : x ≡ y) → Interval → A
intervalElim x y p zero    = x
intervalElim x y p one     = y
intervalElim x y p (seg i) = p i

intervalEta : ∀ {A : Set ℓ} (f : Interval → A) → intervalElim (f zero) (f one) (λ i → f (seg i)) ≡ f
intervalEta f i zero    = f zero
intervalEta f i one     = f one
intervalEta f i (seg j) = f (seg j)

