{-# OPTIONS --cubical #-}

module n2o.N2O where 

open import proto.Base
open import proto.Core
open import proto.IO

open import n2o.Network.WebSocket
open import n2o.Network.Socket
open import n2o.Network.Core
open import n2o.Network.Internal

-- open import Infinity.Proto

postulate 
    terminationCheck : IO ⊤

{-# FOREIGN GHC
import Control.Concurrent (threadDelay)
terminationCheck :: IO ()
terminationCheck = do
    putStrLn "sapere aude"
    threadDelay 1000000
    terminationCheck #-}
    
{-# COMPILE GHC terminationCheck = terminationCheck #-}

data Example : Set where 
    Greet : Example 
    
-- index Init = do 
--   updateText "system" "What is your name?"
--   wire record { id_ = "send" , postback = Just Greet, source = "name" ∷ [] }
-- index (Message Greet) = do 
--   Just name ← get "name"
--   updateText "system" ("Hello, " <> jsEscape name)
index : Event Example → IO ⊤
index ev = putStrLn "Unknown event" -- TODO : monoids

about : Event Example → IO ⊤
about ev = putStrLn "Unknown event"

-- route : Context N2OProto Example → Context N2OProto Example 
-- route c with (unpack (Request.reqPath (Context.cxRequest c)))
-- ... | "/ws/samples/static/index.html" = about
-- ... | "/ws/samples/static/about.html" = about 
-- ... | _ = about

-- router : Context N2OProto Example → Context N2OProto Example 
-- router c = record c { handler = mkHandler route }


-- protocols : 

-- cx : Cx Example
-- cx = mkCx h r m p a d 
--   where h = ?
--         r = ?
--         m = route ∷ []
--         p = []
--         a = ?
--         d = ?
            

main : IO ⊤
main = do 
    -- sock ← socket AF_INET Stream (+ 0)
    hPutStrLn stdout "asd"
    -- protoRun 0 protos
    terminationCheck
    putStrLn "[*] Done"

-- main : IO ⊤
-- main = getLine >>= λ s → putStrLn s
