{-# OPTIONS --without-K #-}

module n2o.Proto.Coinduction where 

open import Agda.Primitive using ( Level )
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Char 
open import Agda.Builtin.Size hiding (∞)

mutual 

  data Delay (A : Set) (i : Size) : Set where 
    now : A → Delay A i 
    later : ∞Delay A i → Delay A i 

  record ∞Delay (A : Set) (i : Size) : Set where 
    coinductive 
    constructor [_]
    field 
      force : {j : Size< i} → Delay A j

data Coℕ : Set where 
  zero : Coℕ
  succ : (n : ∞ Coℕ) → Coℕ
    
infixr 5 _∷_

data Colist {ℓ} (A : Set ℓ) : Set ℓ where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

{-# FOREIGN GHC
    data AgdaColist a    = Nil | Cons a (MAlonzo.RTE.Inf (AgdaColist a))
    type AgdaColist' l a = AgdaColist a #-}

{-# COMPILE GHC Colist = data AgdaColist' (Nil | Cons) #-}
{-# COMPILE UHC Colist = data __LIST__ (__NIL__ | __CONS__) #-}

Costring : Set 
Costring = Colist Char 
