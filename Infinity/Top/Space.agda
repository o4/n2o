{-# OPTIONS --cubical --safe #-}
module Infinity.Top.Space where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Inductive.Empty
open import Infinity.Inductive.One
open import Infinity.Inductive.Two
open import Infinity.Inductive.Fin

open import Infinity.Top.Predicate

record Space : Set₂ where
  constructor space
  field
    C            : Set
    Open         : Pred (Pred C)
    none         : Open (λ _ → ⇑ ⊥)
    all          : Open (λ _ → ⇑ ⊤)
    union        : {A : Set} (f : A → ∃ Open) → Union (π⃐ ∘ f) ∈ Open
    intersection : ∀ {n} (f : Fin n → ∃ Open) → Intersection (π⃐ ∘ f) ∈ Open

  Neighborhood : C → Pred (Pred C)
  Neighborhood x = λ V → ∃ (λ U → (Open U) × (U ⊆ V) × (x ∈ U))

  Closed : Pred (Pred C)
  Closed P = ∀ x → x ∉ P → ∃ (λ U → Neighborhood x U → Disjoint P U)

  Clopen : Pred (Pred C)
  Clopen P = Open P × Closed P


  none-Clopen : Clopen (λ _ → ⇑ ⊥)
  none-Clopen = none , (λ x x∉P → (λ _ → ⇑ ⊤) , (λ N a a∈Empty a∈All → ↓ a∈Empty))

  all-Clopen : Clopen (λ _ → ⇑ ⊤)
  all-Clopen = all , (λ x x∉P → (λ _ → ⇑ ⊥) , (λ N a a∈All a∈Empty → ↓ a∈Empty))

  Complement-closes : ∀ {U : Pred C} → Open U → Closed (Complement U)
  Complement-closes {U} U-open = λ x x∉U → U , (λ N a a∈CU a∈U → a∈CU a∈U)

open Space

preimage : ∀ {A B : Set} → (f : A → B) → Pred B → Pred A
preimage f B = λ a → B (f a)

Continuous : ∀ {{X Y : Space}} → (f : (C X) → (C Y)) → Set₁
Continuous {{X}} {{Y}} f = ∀ B → (Open Y) B → (Open X) (preimage f B)

Discrete : ∀ (A : Set) → Space
Discrete A = space A (λ _ → ⇑ ⊤) (↑ unit) (↑ unit) (λ {A₁} f → ↑ unit) λ {n} f → ↑ unit

Discrete-Clopen : ∀ {A : Set} → ∀ S → Clopen (Discrete A) S
Discrete-Clopen S = ↑ unit , (λ x x∉S → Complement S , (λ N a a∈S a∈CS → a∈CS a∈S))
