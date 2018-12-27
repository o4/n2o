{-# OPTIONS --cubical --type-in-type #-}

module Infinity.Cohesion.Shape where 

variable 𝔸 : Set 

data #∫ (A : Set₀) : Set₀ where 
    #σ  :  A → #∫ A 
    #κ  : (𝔸 → #∫ A) → #∫ A
    #κ' : (𝔸 → #∫ A) → #∫ A

∫ : (A : Set₀) → Set₀
∫ = #∫

module _ {A : Set₀} where 
    σ : A → ∫ A
    σ = #σ

    κ : (𝔸 → ∫ A) → ∫ A
    κ = #κ

    κ′ : (𝔸 → ∫ A) → ∫ A
    κ′ = #κ'

