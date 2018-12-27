{-# OPTIONS --cubical #-}

module Infinity.Cohesion.Im where 

open import Infinity.Proto
open import Infinity.Sigma

postulate 
    ℑ : Set ℓ → Set ℓ
    ι : ∀ {A : Set ℓ} → A → ℑ A 
    
ℑ-unit-at : (A : Set ℓ) → (A → ℑ A)
ℑ-unit-at A = ι {_} {A}

postulate 
  _is-coreduced : Set ℓ → Set ℓ
-- A is-coreduced = ι {_} {A} isEquiv

ℑ-Set₀ : Set₁
ℑ-Set₀ = Σ[ A ∈ Set₀ ] A is-coreduced

ι-ℑ-Set₀ : ℑ-Set₀ → Set₀
ι-ℑ-Set₀ (A , _) = A

postulate 
    ℑ-is-coreduced : (A : Set ℓ) → (ℑ A) is-coreduced 
    
