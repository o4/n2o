{-# OPTIONS --cubical #-}

module n2o.Network.WebSocket where 

open import n2o.Proto.Base
open import n2o.Proto.IO
open import n2o.Network.Internal

{-# FOREIGN GHC import Network.N2O.Web.WebSockets #-}

data N2OProto (A : Set) : Set where 
    Io  : ByteString Strict → ByteString Strict → N2OProto A
    Nop :                                         N2OProto A 

Cx : Set → Set 
Cx = Context N2OProto

CxHandler : Set → Set 
CxHandler a = Cx a → Cx a

-- mkHandler : ∀ {A : Set} (h : Set → IO A) → Set → IO A
-- mkHandler h m = h m >> return Empty -- TODO : monad instance for Result 
  
postulate 
    runServer : ∀ {A : Set} → String → ℤ → Context N2OProto A → IO ⊤
  
{-# COMPILE GHC        Cx =      Network.N2O.Web.WebSockets.Cx                    #-}
{-# COMPILE GHC CxHandler =      Network.N2O.Web.WebSockets.CxHandler             #-}
{-# COMPILE GHC runServer =      Network.N2O.Web.WebSockets.runServer             #-}
{-# COMPILE GHC  N2OProto = data Network.N2O.Web.Websockets.N2OProto ( Io | Nop ) #-}
  
