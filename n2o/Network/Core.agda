module n2o.Network.Core where

open import proto.Base
open import proto.IO

open import n2o.Network.Internal

{-# FOREIGN GHC import Network.N2O.Core #-}

postulate 
    protoRun : ∀ {F : Set → Set} {A : Set} → F A → List (Proto F A) → N2O F A (Result (F A))

{-# COMPILE GHC protoRun = Network.N2O.Core.protoRun #-}
