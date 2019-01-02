{-# OPTIONS --cubical --sized-types --type-in-type #-} -- Oh my Nathaniel Hawthorne

module n2o.Network.Internal where

open import Agda.Builtin.Coinduction

open import n2o.Proto.Base
open import n2o.Proto.Map
open import n2o.Proto.IO

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
  data N2OT {i : Size} (S : Set) (M : Set → Set) (A : Set) : Set where 
    runN2O : S → M A → N2OT {i} S M A 

  N2O : ∀ {i : Size} (F : Set → Set) (A : Set) → Set → Set
  N2O {i} F A = N2OT {i} (State F A) IO 

  record Context {i : Size} (F : Set → Set) (A : Set) : Set where 
    inductive
    constructor mkCx 
    field 
      -- cxHandler    : Event A → N2O F A (Result A) → Context F A -- TODO : Strict Positivity
      cxRequest    : Request → Context F A     
      -- cxMiddleware : List (Context F A → Context F A) -- TODO : Strict Positivity
      -- cxProtos     : ∀ {j : Size< i} → List (Proto {j} F A) -- TODO : Strict Positivity
      cxActions    : ByteString Strict 
      cxDict       : Map (ByteString Strict) (ByteString Strict) 

  State : (F : Set → Set) (A : Set) → Set
  State F A = IORef (Context F A) -- TODO : comp

  record Proto {i : Size} (F : Set → Set) (A : Set) : Set where 
    inductive
    constructor proto
    field 
      protoInfo : ∀ {j : Size< i} F A → N2O {i = j} F A (Result (F A))

{-# COMPILE GHC Context = data Network.N2O.Types.Context (mkCx)                                      #-}
{-# COMPILE GHC  Header = type Network.N2O.Types.Header                                              #-}
{-# COMPILE GHC    N2OT = data Network.N2O.Types.N2OT    ( runN2O                                  ) #-}
{-# COMPILE GHC   Proto = data Network.N2O.Types.Proto   ( protoInfo                               ) #-}
{-# COMPILE GHC   Event = data Network.N2O.Types.Event   ( Init      | Message | Terminate         ) #-}
{-# COMPILE GHC Request = data Network.N2O.Types.Request ( Req ) #-}
{-# COMPILE GHC  Result = data Network.N2O.Types.Result  ( Reply     | Ok      | Unknown   | Empty ) #-}
