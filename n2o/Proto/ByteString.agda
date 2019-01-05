module n2o.Proto.ByteString where

open import n2o.Proto.Core

{-# FOREIGN GHC import Data.ByteString
                import Data.ByteString.Lazy
                import Data.ByteString.Char8 #-}

postulate 
    CoByteString : Set 
    StByteString : Set 
    
{-# COMPILE GHC CoByteString = type Data.ByteString.Lazy.ByteString #-}
{-# COMPILE GHC StByteString = type Data.ByteString.ByteString      #-}

postulate 
  stpack   : String → StByteString 
  stunpack : StByteString → String 
  
{-# COMPILE GHC stpack   = Data.ByteString.Char8.pack   . Data.Text.unpack #-}
-- # COMPILE GHC stunpack = Data.ByteString.Char8.unpack . Data.Text.unpack #
