{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | FFI interface to a node in Rust
module Peras.Node.Netsim.Rust (
  -- * Single Node operations
  RustNode,
  startNode,
  stopNode,
  sendMessage,
  receiveMessage,

  -- * Network operations
  RustNetwork,
  startNetwork,
  tick,
  preferredChain,
  stopNetwork,
)
where

import Control.Exception (bracket)
import Data.Bits ((.<<.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Internal (toForeignPtr0)
import Foreign (Ptr, Storable, Word64, Word8, free, mallocBytes, peekArray, withForeignPtr)
import Foreign.C (CInt, CString, withCString)
import Foreign.Storable (Storable (..))
import Peras.Chain (Chain)
import Peras.IOSim.Network.Types (Topology)
import Peras.IOSim.Protocol.Types (Protocol)
import Peras.IOSim.Simulate.Types (Parameters)
import Peras.Message (NodeId (..))
import System.Random (StdGen)

newtype RustNode = RustNode {foreignNode :: Ptr PerasNode}

data PerasNode

foreign import capi unsafe "peras.h start_node" c_start_node :: CString -> Double -> Double -> IO (Ptr PerasNode)

foreign import capi unsafe "peras.h stop_node" c_stop_node :: Ptr PerasNode -> IO ()

foreign import capi unsafe "peras.h send_message" c_send_message :: Ptr PerasNode -> Ptr Word8 -> Int -> IO ()

foreign import capi unsafe "peras.h receive_message" c_receive_message :: Ptr PerasNode -> Ptr Word8 -> Int -> IO Int

-- | Start a `RustNode` with given id and amount of stake.
startNode :: NodeId -> Integer -> Integer -> IO RustNode
startNode MkNodeId{nodeId} nodeStake totalStake =
  withCString nodeId $ \cstr ->
    RustNode <$> c_start_node cstr (fromIntegral nodeStake) (fromIntegral totalStake)

-- | Stop given `RustNode`.
stopNode :: RustNode -> IO ()
stopNode RustNode{foreignNode} =
  c_stop_node foreignNode

-- | Send a message to this node.
-- Node must have been started before through `startNode` and not be `NULL`.
sendMessage :: RustNode -> ByteString -> IO ()
sendMessage RustNode{foreignNode} bytes =
  let (foreignPtr, len) = toForeignPtr0 bytes
   in withForeignPtr foreignPtr $ \ptr ->
        c_send_message foreignNode ptr len

bufferSize :: Int
bufferSize = 1 .<<. 16

receiveMessage :: RustNode -> IO ByteString
receiveMessage RustNode{foreignNode} = do
  bracket (mallocBytes bufferSize) free $ \ptr -> do
    len <- c_receive_message foreignNode ptr bufferSize
    BS.pack <$> peekArray len ptr

newtype RustNetwork = RustNetwork {foreignNetwork :: Ptr Netsim}

data Netsim

foreign import capi unsafe "peras.h start_network" c_start_network :: CString -> CString -> Word64 -> IO (Ptr Netsim)
foreign import capi unsafe "peras.h stop_network" c_stop_network :: Ptr Netsim -> IO ()
foreign import capi unsafe "peras.h broadcast" c_broadcast :: Ptr Netsim -> Ptr Word8 -> Int -> IO ()
foreign import capi unsafe "peras.h get_preferred_chain" c_get_preferred_chain :: Ptr Netsim -> CString -> Ptr Word8 -> Int -> IO Int

-- | Start network with given `Topology` and `Parameters` serialised to JSON.
-- Parameter seed is used to make the internal random generator used in Rust
-- deterministic.
startNetwork :: ByteString -> ByteString -> Word64 -> IO RustNetwork
startNetwork parameters topology seed = undefined

tick :: RustNetwork -> IO ()
tick RustNetwork{foreignNetwork} = undefined

preferredChain :: RustNetwork -> NodeId -> IO ByteString
preferredChain = undefined

stopNetwork :: RustNetwork -> IO ()
stopNetwork = undefined
