{-# OPTIONS --cubical --safe #-}

module n2o.Proto.Base where 

open import Agda.Builtin.Int public
  using ()
  renaming
  ( Int to ℤ
  ; pos    to +_
  ; negsuc to -[1+_] )

data _×_ (a b : Set) : Set where 
  pair : a → b → a × b 
