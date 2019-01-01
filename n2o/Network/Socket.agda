module n2o.Network.Socket where 

open import n2o.Proto.IO
open import n2o.Proto.Base

data SocketType : Set where 
    NoSocketType : SocketType 
    Stream     : SocketType 
    Datagram   : SocketType 
    Raw        : SocketType 
    RDM        : SocketType 
    SeqPacket  : SocketType 
    
{-# COMPILE GHC SocketType = data Network.Socket.SocketType
                           ( NoSocketType
                           | Stream
                           | Datagram
                           | Raw
                           | RDM
                           | SeqPacket ) #-}
                           
data SockFamily : Set where 
    AF_UNSPEC           : SockFamily
    AF_UNIX             : SockFamily
    AF_INET             : SockFamily
    AF_INET6            : SockFamily
    AF_IMPLINK          : SockFamily
    AF_PUP              : SockFamily
    AF_CHAOS            : SockFamily
    AF_NS               : SockFamily
    AF_NBS              : SockFamily
    AF_ECMA             : SockFamily
    AF_DATAKIT          : SockFamily
    AF_CCITT            : SockFamily
    AF_SNA              : SockFamily
    AF_DECnet           : SockFamily
    AF_DLI              : SockFamily
    AF_LAT              : SockFamily
    AF_HYLINK           : SockFamily
    AF_APPLETALK        : SockFamily
    AF_ROUTE            : SockFamily
    AF_NETBIOS          : SockFamily
    AF_NIT              : SockFamily
    AF_EIE              : SockFamily
    AF_ISO              : SockFamily
    AF_OSI              : SockFamily
    AF_NETMAN           : SockFamily
    AF_X25              : SockFamily
    AF_AX25             : SockFamily
    AF_OSINET           : SockFamily
    AF_GOSSIP           : SockFamily
    AF_IPX              : SockFamily
    Pseudo_AF_XTP       : SockFamily
    AF_CTF              : SockFamily
    AF_WAN              : SockFamily
    AF_SDL              : SockFamily
    AF_NETWARE          : SockFamily
    AF_NDD              : SockFamily
    AF_INTF             : SockFamily
    AF_COIP             : SockFamily
    AF_CNT              : SockFamily
    Pseudo_AF_RTIP      : SockFamily
    Pseudo_AF_PIP       : SockFamily
    AF_SIP              : SockFamily
    AF_ISDN             : SockFamily
    Pseudo_AF_KEY       : SockFamily
    AF_NATM             : SockFamily
    AF_ARP              : SockFamily
    Pseudo_AF_HDRCMPLT  : SockFamily
    AF_ENCAP            : SockFamily
    AF_LINK             : SockFamily
    AF_RAW              : SockFamily
    AF_RIF              : SockFamily
    AF_NETROM           : SockFamily
    AF_BRIDGE           : SockFamily
    AF_ATMPVC           : SockFamily
    AF_ROSE             : SockFamily
    AF_NETBEUI          : SockFamily
    AF_SECURITY         : SockFamily
    AF_PACKET           : SockFamily
    AF_ASH              : SockFamily
    AF_ECONET           : SockFamily
    AF_ATMSVC           : SockFamily
    AF_IRDA             : SockFamily
    AF_PPPOX            : SockFamily
    AF_WANPIPE          : SockFamily
    AF_BLUETOOTH        : SockFamily
    AF_CAN              : SockFamily
 
{-# COMPILE GHC SockFamily = data Network.Socket.Family
                             ( AF_UNSPEC
                             | AF_UNIX
                             | AF_INET
                             | AF_INET6
                             | AF_IMPLINK
                             | AF_PUP
                             | AF_CHAOS
                             | AF_NS
                             | AF_NBS
                             | AF_ECMA
                             | AF_DATAKIT
                             | AF_CCITT
                             | AF_SNA
                             | AF_DECnet
                             | AF_DLI
                             | AF_LAT
                             | AF_HYLINK
                             | AF_APPLETALK
                             | AF_ROUTE
                             | AF_NETBIOS
                             | AF_NIT
                             | AF_802
                             | AF_ISO
                             | AF_OSI
                             | AF_NETMAN
                             | AF_X25
                             | AF_AX25
                             | AF_OSINET
                             | AF_GOSSIP
                             | AF_IPX
                             | Pseudo_AF_XTP
                             | AF_CTF
                             | AF_WAN
                             | AF_SDL
                             | AF_NETWARE
                             | AF_NDD
                             | AF_INTF
                             | AF_COIP
                             | AF_CNT
                             | Pseudo_AF_RTIP
                             | Pseudo_AF_PIP
                             | AF_SIP
                             | AF_ISDN
                             | Pseudo_AF_KEY
                             | AF_NATM
                             | AF_ARP
                             | Pseudo_AF_HDRCMPLT
                             | AF_ENCAP
                             | AF_LINK
                             | AF_RAW
                             | AF_RIF
                             | AF_NETROM
                             | AF_BRIDGE
                             | AF_ATMPVC
                             | AF_ROSE
                             | AF_NETBEUI
                             | AF_SECURITY
                             | AF_PACKET
                             | AF_ASH
                             | AF_ECONET
                             | AF_ATMSVC
                             | AF_IRDA
                             | AF_PPPOX
                             | AF_WANPIPE
                             | AF_BLUETOOTH
                             | AF_CAN ) #-}
                             
data SocketOption : Set where 
  Debug         : SocketOption
  ReuseAddr     : SocketOption
  Type          : SocketOption
  SoError       : SocketOption
  DontRoute     : SocketOption
  Broadcast     : SocketOption
  SendBuffer    : SocketOption
  RecvBuffer    : SocketOption
  KeepAlive     : SocketOption
  OOBInline     : SocketOption
  TimeToLive    : SocketOption
  MaxSegment    : SocketOption
  NoDelay       : SocketOption
  Cork          : SocketOption
  Linger        : SocketOption
  ReusePort     : SocketOption
  RecvLowWater  : SocketOption
  SendLowWater  : SocketOption
  RecvTimeOut   : SocketOption
  SendTimeOut   : SocketOption
  UseLoopBack   : SocketOption
  UserTimeout   : SocketOption
  IPv6Only      : SocketOption
  CustomSockOpt : ℤ × ℤ → SocketOption
  
{-
{-# COMPILE GHC SocketOption = data Network.Socket.SocketOption
                                ( Debug
                                | ReuseAddr
                                | Type
                                | SoError
                                | DontRoute
                                | Broadcast
                                | SendBuffer
                                | RecvBuffer
                                | KeepAlive
                                | OOBInline
                                | TimeToLive
                                | MaxSegment
                                | NoDelay
                                | Cork
                                | Linger
                                | ReusePort
                                | RecvLowWater
                                | SendLowWater
                                | RecvTimeOut
                                | SendTimeOut
                                | UseLoopBack
                                | UserTimeout
                                | IPv6Only
                                | CustomSockOpt ) #-}
-}

postulate 
    Family : Set 
    Socket : Set 

{-# COMPILE GHC Family = type Network.Socket.Family #-}
{-# COMPILE GHC Socket = type Network.Socket.Socket #-}

ProtocolNumber : Set 
ProtocolNumber = ℤ

data SocketStatus : Set where 
  NotConnected      : SocketStatus 
  Bound             : SocketStatus 
  Listening         : SocketStatus 
  Connected         : SocketStatus 
  ConvertedToHandle : SocketStatus 
  Closed            : SocketStatus 
  
{-# COMPILE GHC SocketStatus = data Network.Socket.SocketStatus
  ( NotConnected
  | Bound
  | Listening
  | Connected
  | ConvertedToHandle
  | Closed ) #-}
  
-- data SockAddr where 
--   SockAddrInet   : PortNumber → HostAddress → SockAddr 
--   SockAddrInet6  : PortNumber → FlowInfo → HostAddress6 → ScopeID → SockAddr 
--   SockAddrUnix   : String → SockAddr 
--   SockAddrCan    : ℤ → SockAddr 


-- record Socket : Set where 
--     constructor MkSocket 
--     field 
--         sock     : ℤ
--         family   : Family
--         type     : SocketType
--         protonum : ProtocolNumber
--         status   : MVar SocketStatus 
-- open Socket 

-- {-# COMPILE GHC Socket = #-}

{-# FOREIGN GHC
  import Unsafe.Coerce 
  import Foreign.C.Types
  import Network.Socket 

  coeCInt :: Integer -> Foreign.C.Types.CInt
  coeCInt n = Unsafe.Coerce.unsafeCoerce (n :: Integer) :: Foreign.C.Types.CInt
#-}

postulate 
    socket : SockFamily → SocketType → ProtocolNumber → IO Socket
    -- setSocketOption : Socket → SocketOption → ℤ → IO ⊤
    -- bind   : Socket → SockAddr → IO ⊤   
    -- listen : Socket → ℤ → IO ⊤
    -- accept : Socket → IO (Socket × SockAddr)
    
{-# COMPILE GHC socket = \ f t n -> Network.Socket.socket f t (coeCInt n) #-}
