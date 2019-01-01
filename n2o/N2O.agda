{-# OPTIONS --cubical #-}

module n2o.N2O where 

open import n2o.Proto.Base
open import n2o.Proto.Core
open import n2o.Proto.IO

open import n2o.Network.Socket
open import n2o.Network.Core
open import n2o.Network.Types

-- open import Infinity.Proto

postulate 
    terminationCheck : IO ⊤

{-# FOREIGN GHC
import Control.Concurrent (threadDelay)
terminationCheck :: IO ()
terminationCheck = do
    putStrLn "."
    threadDelay 1000000
    terminationCheck #-}
    
{-# COMPILE GHC terminationCheck = terminationCheck #-}

main : IO ⊤
main = do 
    -- sock ← socket AF_INET Stream (+ 0)
    hPutStrLn stdout "asd"
    -- protoRun 0 protos
    terminationCheck
    putStrLn "[*] Done"

-- main : IO ⊤
-- main = getLine >>= λ s → putStrLn s
