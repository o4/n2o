module n2o.Network.Core where

open import n2o.Proto.IO
open import n2o.Proto.Base
open import n2o.Network.Types

{-# FOREIGN GHC import Network.N2O.Core #-}

postulate 
    protoRun : ∀ {F : Set → Set} {A : Set} → F A → List (Proto F A) → N2O F A (Result (F A))

{-# COMPILE GHC protoRun = Network.N2O.Core.protoRun #-}
