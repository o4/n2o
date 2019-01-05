{-# OPTIONS --cubical #-}

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
              
open import Agda.Builtin.Size public
  using    ( Size ; Size<_ ; ↑_ ; ∞ )
  renaming ( SizeU to SizeUniv )
  
open import Agda.Builtin.String public 
  using ( String ; primShowString ; primStringAppend )

open import Agda.Builtin.Unit public 
open import Agda.Builtin.IO public 

variable
    ℓ  : Level
    ℓ₁ : Level
    ℓ₂ : Level
    ℓ₃ : Level
    ℓ₄ : Level

data _×_ (a b : Set) : Set where 
  pair : a → b → a × b 
