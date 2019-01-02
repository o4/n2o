module n2o.Proto.ByteString where

open import n2o.Proto.Core

{-# FOREIGN GHC import Data.ByteString.Lazy
                import Data.ByteString.Strict #-}

postulate 
    CoByteString : Set 
    StByteString : Set 
    
{-# COMPILE GHC CoByteString = type Data.ByteString.Lazy.ByteString   #-}
{-# COMPILE GHC StByteString = type Data.ByteString.Strict.ByteString #-}
