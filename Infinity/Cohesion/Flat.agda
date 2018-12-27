{-# OPTIONS --without-K --cubical #-}

module Infinity.Cohesion.Flat where 

open import Infinity.Proto
open import Infinity.Univ

-- data Crisp {ℓ : Level} (A : Set ℓ) : Set ℓ where 
    -- _is-crisp : A → Crisp A 

_is-crisp : Set ℓ → Set ℓ
A is-crisp = A

data ♭ (A : Set ℓ) : Set ℓ where 
    _^♭ : (a : A is-crisp) → ♭ A

♭-ind : ∀ {ç : Level} {ℓ : Level is-crisp} {A : Set ℓ is-crisp} 
      → (C : ♭ A → Set ç) → ((u : A is-crisp) → C (u ^♭)) → (x : ♭ A) → C x
♭-ind _ f (x ^♭) = f x

♭-counit : ∀ {ℓ : Level is-crisp} {A : Set ℓ is-crisp} → ♭ A → A
♭-counit (a ^♭) = a

♭-counit-at : ∀ (A : Set₀ is-crisp) → ♭ A → A 
♭-counit-at A = ♭-counit {_} {A}

postulate _is-discrete : ∀ (A : Set₀ is-crisp) → Set₀
-- A is-discrete = isEquiv (♭-counit-at A)

postulate ♭-indempotent : ∀ (A : Set₀ is-crisp) → (♭ A) is-crisp

let♭ : ∀ {A : Set ℓ₁ is-crisp} {C : ♭ A → Set ℓ₂ is-crisp} 
     → (s : ♭ A) → (t : (u : A is-crisp) → C (u ^♭)) → C s 
let♭ (a ^♭) t = t a

let♭' : ∀ {A : Set ℓ₁ is-crisp} {C : ♭ A → Set ℓ₂ is-crisp} 
     → (s : ♭ A) → (t : (u : A is-crisp) → C (u ^♭)) → C s 
let♭' {C = C} x t = let♭ {C = C} x t

syntax let♭ s (λ u → τ) = let♭ u ^♭≔ s in♭ τ
syntax let♭' {C = C} s (λ u → τ) = let♭' u ^♭≔ s in♭ τ ∈ C

♭-map : ∀ {A B : Set₀ is-crisp} → (f : (A → B) is-crisp) → (♭ A → ♭ B)
♭-map f (a ^♭) = (f a) ^♭
