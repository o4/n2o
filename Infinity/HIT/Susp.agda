{-# OPTIONS --cubical --safe #-}

module Infinity.HIT.Susp where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Path
open import Infinity.Inductive.Two
open import Infinity.Equiv
open import Infinity.Univ
open import Infinity.HIT.S1
open import Infinity.HIT.S2

open import Agda.Builtin.Bool public

data Susp (A : Set ℓ) : Set ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

SuspBool : Set
SuspBool = Susp Bool

SuspBool→S¹ : SuspBool → S¹
SuspBool→S¹ north = base
SuspBool→S¹ south = base
SuspBool→S¹ (merid false i) = loop i
SuspBool→S¹ (merid true i)  = base

S¹→SuspBool : S¹ → SuspBool
S¹→SuspBool base     = north
S¹→SuspBool (loop i) = trans (merid false) (sym (merid true)) i

SuspBool→S¹→SuspBool : (x : SuspBool) → Path _ (S¹→SuspBool (SuspBool→S¹ x)) x
SuspBool→S¹→SuspBool north = refl
SuspBool→S¹→SuspBool south = merid true 
SuspBool→S¹→SuspBool (merid false i) = λ j → hcomp (λ k → (λ { (j = i1) → merid false i
                                                             ; (i = i0) → north
                                                             ; (i = i1) → merid true (j ∨ ~ k)}))
                                                   (merid false i)
SuspBool→S¹→SuspBool (merid true i)  = λ j → merid true (i ∧ j)

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base     = refl
S¹→SuspBool→S¹ (loop i) = λ j →
  hfill (λ k → \ { (i = i0) → base; (i = i1) → base }) (inc (loop i)) (~ j)

S¹≃SuspBool : S¹ ≃ SuspBool
S¹≃SuspBool = isoToEquiv S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹

S¹≡SuspBool : S¹ ≡ SuspBool
S¹≡SuspBool = isoToPath S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹


-- Now the sphere

SuspS¹ : Set
SuspS¹ = Susp S¹

-- SuspS¹→S² : SuspS¹ → S²
-- SuspS¹→S² north = base
-- SuspS¹→S² south = base
-- SuspS¹→S² (merid a i) = {!!}

S²→SuspS¹ : S² → SuspS¹
S²→SuspS¹ base = north
S²→SuspS¹ (surf i j) = hcomp (λ k → λ { (i = i0) → north
                                      ; (i = i1) → merid base (~ k)
                                      ; (j = i0) → merid base (~ k ∧ i)
                                      ; (j = i1) → merid base (~ k ∧ i) })
                             (merid (loop j) i)
