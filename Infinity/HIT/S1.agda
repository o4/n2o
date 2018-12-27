{-# OPTIONS --cubical --rewriting #-}

module Infinity.HIT.S1 where

open import Infinity.Core
open import Infinity.Proto
open import Infinity.Path public
open import Infinity.Equiv public
open import Infinity.Univ public
open import Infinity.Inductive.Z

data S¹ : Set where
   base : S¹
   loop : base ≡ base

ΩS¹ : Set
ΩS¹ = base ≡ base

helix : S¹ → Set
helix base = ℤ
helix (loop i) = sucPathInt i

loopS¹ : Set 
loopS¹ = base ≡ base 

invloop : base ≡ base 
invloop = λ i → loop (~ i)

_∘S¹_ : loopS¹ → loopS¹ → loopS¹ 
_∘S¹_ = trans

module S¹-Elim {P : S¹ → Set ℓ} (base* : P base) (loop* : PathP (λ i → P (loop i)) base* base*) where 
  postulate S¹-elim : ∀ x → P x 

open S¹-Elim public

π₁S¹ : Set 
π₁S¹ = base ≡ base 

oneTurn : ∀ {l : loopS¹} → loopS¹
oneTurn {l = l} = l ∘S¹ loop

invTurn : ∀ {l : loopS¹} → loopS¹
invTurn {l = l} = l ∘S¹ invloop

loop̂⁻¹ᵢ : ℕ → loopS¹
loop̂⁻¹ᵢ zero = invloop
loop̂⁻¹ᵢ (succ n) = invTurn {l = loop̂⁻¹ᵢ n}

natLoop : ℕ → base ≡ base 
natLoop zero    = refl 
natLoop (succ n) = trans (natLoop n) loop

intLoop : ℤ → base ≡ base 
intLoop (pos    n) = natLoop n 
intLoop (negsuc n) = sym (natLoop (succ n))

-- Hopf prerequisites

rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j = hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k) ; (i = i1) → loop (j ∧ k)
                                    ; (j = i0) → loop (i ∨ ~ k) ; (j = i1) → loop (i ∧ k) }) base

rot : S¹ → S¹ → S¹
rot base x     = x
rot (loop i) x = rotLoop x i

isPropFamS¹ : (P : S¹ → Set ℓ) (pP : (x : S¹) → isProp (P x)) (b0 : P base) → PathP (λ i → P (loop i)) b0 b0
isPropFamS¹ P pP b0 i = pP (loop i) (transp (λ j → P (loop (i ∧ j))) (~ i) b0) (transp (λ j → P (loop (i ∨ ~ j))) i b0) i

rotIsEquiv : (a : S¹) → isEquiv (rot a)
rotIsEquiv base = idIsEquiv S¹
rotIsEquiv (loop i) = isPropFamS¹ (λ x → isEquiv (rot x)) (λ x → isPropIsEquiv (rot x)) (idIsEquiv _) i

rotLoopInv : (a : S¹) → PathP (λ i → rotLoop (rotLoop a (~ i)) i ≡ a) refl refl
rotLoopInv a i j = hcomp (λ k → λ { (i = i0) → a;
                                    (i = i1) → rotLoop a (j ∧ ~ k);
                                    (j = i0) → rotLoop (rotLoop a (~ i)) i;
                                    (j = i1) → rotLoop a (i ∧ ~ k)} ) (rotLoop (rotLoop a ((~ i) ∨ j)) i)

rotLoopEquiv : (i : I) → S¹ ≃ S¹
rotLoopEquiv i = isoToEquiv (λ a → rotLoop a i) (λ a → rotLoop a (~ i)) (λ a → rotLoopInv a i) (λ a → rotLoopInv a (~ i))
