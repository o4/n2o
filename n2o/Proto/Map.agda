module n2o.Proto.Map where 

{-# FOREIGN GHC import Data.Map #-}

postulate 
  Map : Set → Set → Set 
  
{-# COMPILE GHC Map = type Data.Map.Map #-}
