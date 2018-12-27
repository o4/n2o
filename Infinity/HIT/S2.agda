{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.S2 where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Path

data S² : Set where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl
