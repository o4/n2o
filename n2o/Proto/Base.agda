{-# OPTIONS --cubical #-}

module n2o.Proto.Base where 

open import Agda.Builtin.Int public
  using ()
  renaming
  ( Int to ℤ
  ; pos    to +_      -- "+ n"      stands for "n"
  ; negsuc to -[1+_]  -- "-[1+ n ]" stands for "- (1 + n)"
  )
