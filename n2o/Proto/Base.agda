{-# OPTIONS --safe #-}

module n2o.Proto.Base where 

open import n2o.Proto.Core public 
open import n2o.Proto.ByteString
open import n2o.Proto.Map
open import n2o.Proto.IO

data Strictness : Set where 
    Lazy   : Strictness 
    Strict : Strictness 
    
ByteString : Strictness → Set 
ByteString Strict = StByteString 
ByteString Lazy   = CoByteString
