{-# OPTIONS --cubical --safe #-}
module Infinity.Group.Hopf where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Path
open import Infinity.Equiv public
open import Infinity.Univ
open import Infinity.HIT.S1
open import Infinity.HIT.S2
open import Infinity.HIT.Susp

-- Hopf fibration using S²
HopfS² : S² → Set
HopfS² base = S¹
HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                               ; (i = i1) → _ , idEquiv S¹
                               ; (j = i0) → _ , idEquiv S¹
                               ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

-- Hopf fibration using more direct definition of the rot equivalence
HopfS²' : S² → Set
HopfS²' base = S¹
HopfS²' (surf i j) = Glue S¹ (λ { (i = i0) → _ , rotLoopEquiv i0
                                ; (i = i1) → _ , rotLoopEquiv i0
                                ; (j = i0) → _ , rotLoopEquiv i0
                                ; (j = i1) → _ , rotLoopEquiv i } )

-- Hopf fibration using suspension of S¹
HopfSuspS¹ : SuspS¹ → Set
HopfSuspS¹ north = S¹
HopfSuspS¹ south = S¹
HopfSuspS¹ (merid x i) = ua (_ , rotIsEquiv x) i

