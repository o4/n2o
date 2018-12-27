{-# OPTIONS --cubical --safe #-}

module Infinity.Top.Predicate where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Inductive.Empty

Pred : ∀ {ℓ} → Set ℓ → Set (ℓ-succ ℓ)
Pred {ℓ} A = A → Set ℓ

module _ {A : Set ℓ} where
    _∈_ : A → Pred A → Set _
    x ∈ P = P x

    _∉_ : A → Pred A → Set _
    x ∉ P = ¬ x ∈ P

    _⊆_ : Pred A → Pred A → Set _
    P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

    _⊈_ : Pred A → Pred A → Set _
    P ⊈ Q = ¬ (P ⊆ Q)

    _⊂_ : Pred A → Pred A → Set _
    P ⊂ Q = (P ⊆ Q) × (Q ⊈ P)

    _⊄_ : Pred A → Pred A → Set _
    P ⊄ Q = ¬ (P ⊂ Q)

Union : ∀ {A I : Set ℓ} → (I → Pred A) → Pred A
Union {I} F = λ a → ∃ (λ i → a ∈ F i)

Intersection : ∀ {A I : Set ℓ} → (I → Pred A) → Pred A
Intersection F = λ a → ∀ i → a ∈ F i

Complement : ∀ {A : Set ℓ} → Pred A → Pred A
Complement A = λ a → a ∉ A

Disjoint : ∀ {A : Set} → Pred A → Pred A → Set
Disjoint A B = ∀ a → a ∈ A → a ∉ B
