module n2o.Network.Types where

open import n2o.Proto.Base
open import n2o.Proto.IO

{-# FOREIGN GHC import Network.N2O.Types #-}

postulate 
  Header : Set 
  
{-# COMPILE GHC Header = type Network.N2O.Types.Header #-}

data Event (A : Set ℓ) : Set ℓ where
  Init      :     Event A 
  Message   : A → Event A 
  Terminate :     Event A 
  
{-# COMPILE GHC Event = data Network.N2O.Types.Event ( Init | Message | Terminate ) #-}

data Result (A : Set ℓ) : Set ℓ where
  Reply   : A → Result A 
  Ok      :     Result A 
  Unknown :     Result A 
  Empty   :     Result A 

{-# COMPILE GHC Result = data Network.N2O.Types.Result ( Reply | Ok | Unknown | Empty ) #-}

postulate 
  Context : (F : Set → Set) (A : Set) → Set
  
{-# COMPILE GHC Context = type Network.N2O.Types.Context #-}

State : (F : Set → Set) (A : Set) → Set
State F A = IORef (Context F A) -- TODO : comp

data N2OT (S : Set) (M : Set → Set) (A : Set) : Set where 
  runN2O : S → M A → N2OT S M A 

{-# COMPILE GHC N2OT = data Network.N2O.Types.N2OT ( runN2O ) #-}

N2O : (F : Set → Set) (A : Set) → Set → Set
N2O F A = N2OT (State F A) IO 

record Proto (F : Set → Set) (A : Set) : Set where 
  constructor proto
  field 
    protoInfo : F A → N2O F A (Result (F A))

{-# COMPILE GHC Proto = data Network.N2O.Types.Proto ( protoInfo ) #-}
