{-# OPTIONS --cubical --safe #-}

module n2o.Proto.Core where 

open import Agda.Builtin.Int public
  using ()
  renaming
  ( Int to ℤ
  ; pos    to +_
  ; negsuc to -[1+_] )

open import Agda.Builtin.List public
  using ( List ; [] ; _∷_ )

open import Agda.Primitive public
     using    ( Level ; _⊔_ ; Setω )
     renaming ( lzero to ℓ-zero
              ; lsuc  to ℓ-succ )

variable
    ℓ  : Level
    ℓ₁ : Level
    ℓ₂ : Level
    ℓ₃ : Level
    ℓ₄ : Level

data _×_ (a b : Set) : Set where 
  pair : a → b → a × b 
