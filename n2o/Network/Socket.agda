module n2o.Network.Socket where 

open import n2o.Proto.IO
open import n2o.Proto.Base

{-# FOREIGN GHC import Network.Socket.Types #-}

data SocketType : Set where 
    NoSocketType : SocketType 
    Stream     : SocketType 
    Datagram   : SocketType 
    Raw        : SocketType 
    RDM        : SocketType 
    Seq        : SocketType 
    
{-# COMPILE GHC SocketType = data Network.Socket.Types.SocketType
                           ( NoSocketType
                           | Stream
                           | Datagram
                           | Raw
                           | RDM
                           | Seq ) #-}
                           
data SockFamily : Set where 
    AF_UNSPEC   : SockFamily
    AF_UNIX     : SockFamily
    AF_INET     : SockFamily
    AF_INET6    : SockFamily
    AF_IMPLINK  : SockFamily
    AF_PUP      : SockFamily
 
{-# COMPILE GHC SockFamily = data Network.Socket.Types.Family
                             ( AF_UNSPEC
                             | AF_UNIX
                             | AF_INET
                             | AF_INET6
                             | AF_IMPLINK
                             | AF_PUP ) #-}

postulate 
    Family : Set 
    Socket : Set 

{-# COMPILE GHC Family = type Network.Socket.Types.Family #-}
{-# COMPILE GHC Socket = type Network.Socket.Types.Socket #-}

ProtocolNumber : Set 
ProtocolNumber = ℤ

-- record Socket : Set where 
--     constructor MkSocket 
--     field 
--         sock     : Int
--         family   : Family
--         type     : SocketType
--         protonum : ProtocolNumber
--         -- Socket status MVar
-- open Socket 

-- {-# COMPILE GHC Socket = #-}

postulate 
    socket : SockFamily → SocketType → ProtocolNumber → IO Socket
    
{-# COMPILE GHC socket = \ _ -> Network.Socket.socket :: Family -> SocketType -> ProtocolNumber -> IO Socket #-}
