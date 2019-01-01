module n2o.Proto.ByteString where

open import n2o.Proto.Core

{-# FOREIGN GHC import Data.ByteString.Lazy   as BL
                import Data.ByteString.String as BS #-}

postulate 
    ByteStringLazy   : Set 
    ByteStringStrict : Set 
    
{-# COMPILE GHC ByteStringLazy   = BL.ByteString #-}
{-# COMPILE GHC ByteStringStrict = BS.ByteString #-}
