{-# OPTIONS --cubical #-}

module n2o.N2O where 

open import n2o.Proto.Base
open import n2o.Proto.IO
open import n2o.Network.Socket

-- open import Infinity.Proto

main : IO ⊤
main = do 
    -- sock ← socket AF_INET Stream (ℤ.pos 0)
    hPutStrLn stdout "asd"
    putStrLn "[*] Done"

-- main : IO ⊤
-- main = getLine >>= λ s → putStrLn s
