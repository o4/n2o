{-# OPTIONS --cubical --sized-types --type-in-type #-} -- Oh my Nathaniel Hawthorne

module n2o.Network.Internal where

open import proto.Base
open import proto.Map
open import proto.IO

{-# FOREIGN GHC import Network.N2O.Types #-}

postulate 
  Header : Set 
  
data Event (A : Set) : Set where
  Init      :     Event A 
  Message   : A → Event A 
  Terminate :     Event A 
  
data Result (A : Set) : Set where
  Reply   : A → Result A 
  Ok      :     Result A 
  Unknown :     Result A 
  Empty   :     Result A 

record Request : Set where 
  constructor Req 
  field 
    reqPath : ByteString Strict 
    reqMeth : ByteString Strict 
    reqVers : ByteString Strict 
    reqHead : List Header 

mutual 
  data N2OT (S : Set) (M : Set → Set) (A : Set) : Set where 
    runN2O : S → M A → N2OT S M A 

  N2O : (F : Set → Set) (A : Set) → Set → Set
  N2O F A = N2OT (State F A) IO 
  -- N2O F A = ReaderT (IORef (Context F A)) IO 

  {-# NO_POSITIVITY_CHECK #-}
  record Context (F : Set → Set) (A : Set) : Set where 
    constructor mkCx 
    field 
      cxHandler    : Event A → N2O F A (Result A) → Context F A   -- TODO : Strict Positivity
      cxRequest    : Request
      cxMiddleware : List (Context F A → Context F A)             -- TODO : Strict Positivity
      cxProtos     : List (Proto F A)                             -- TODO : Strict Positivity
      cxActions    : ByteString Strict 
      cxDict       : Map (ByteString Strict) (ByteString Strict) 

  State : (F : Set → Set) (A : Set) → Set
  State F A = IORef (Context F A) -- TODO : comp

  record Proto (F : Set → Set) (A : Set) : Set where 
    inductive
    constructor proto
    field 
      protoInfo : F A → N2O F A (Result (F A))

{-# COMPILE GHC Context = data Network.N2O.Types.Context (mkCx)                                      #-}
{-# COMPILE GHC  Header = type Network.N2O.Types.Header                                              #-}
{-# COMPILE GHC    N2OT = data Network.N2O.Types.N2OT    ( runN2O                                  ) #-}
{-# COMPILE GHC   Proto = data Network.N2O.Types.Proto   ( protoInfo                               ) #-}
{-# COMPILE GHC   Event = data Network.N2O.Types.Event   ( Init      | Message | Terminate         ) #-}
{-# COMPILE GHC Request = data Network.N2O.Types.Request ( Req                                     ) #-}
{-# COMPILE GHC  Result = data Network.N2O.Types.Result  ( Reply     | Ok      | Unknown   | Empty ) #-}
