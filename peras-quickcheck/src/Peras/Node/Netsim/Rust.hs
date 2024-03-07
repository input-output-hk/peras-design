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
  RustNetwork (RustNetwork, tick),
  startNetwork,
  broadcast,
  preferredChain,
  stopNetwork,
)
where

import Control.Exception (bracket)
import Data.Bits ((.<<.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Internal (toForeignPtr0)
import Data.IORef (IORef, newIORef)
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8)
import Foreign (Ptr, Word64, Word8, free, mallocBytes, peekArray, withForeignPtr)
import Foreign.C (CString, withCString)
import Peras.Message (NodeId (..))

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

data RustNetwork = RustNetwork
  { tick :: IORef Word64
  , foreignNetwork :: Ptr Netsim
  }

data Netsim

foreign import capi unsafe "peras.h start_network" c_start_network :: CString -> CString -> IO (Ptr Netsim)
foreign import capi unsafe "peras.h stop_network" c_stop_network :: Ptr Netsim -> IO ()
foreign import capi unsafe "peras.h broadcast" c_broadcast :: Ptr Netsim -> Ptr Word8 -> Int -> IO ()
foreign import capi unsafe "peras.h get_preferred_chain" c_get_preferred_chain :: Ptr Netsim -> CString -> Ptr Word8 -> Int -> IO Int

-- | Start network with given `Topology` and `Parameters` serialised to JSON.
startNetwork :: ByteString -> ByteString -> IO RustNetwork
startNetwork topology parameters =
  withCString (Text.unpack $ decodeUtf8 topology) $ \ctopology ->
    withCString (Text.unpack $ decodeUtf8 parameters) $ \cparams ->
      RustNetwork <$> newIORef 0 <*> c_start_network ctopology cparams

broadcast :: RustNetwork -> ByteString -> IO ()
broadcast RustNetwork{foreignNetwork} bytes =
  let (foreignPtr, len) = toForeignPtr0 bytes
   in withForeignPtr foreignPtr $ \ptr ->
        c_broadcast foreignNetwork ptr len

preferredChain :: RustNetwork -> NodeId -> IO ByteString
preferredChain RustNetwork{foreignNetwork} MkNodeId{nodeId} =
  bracket (mallocBytes bufferSize) free $ \ptr -> do
    len <- withCString nodeId $ \cstr ->
      c_get_preferred_chain foreignNetwork cstr ptr bufferSize
    BS.pack <$> peekArray len ptr

stopNetwork :: RustNetwork -> IO ()
stopNetwork RustNetwork{foreignNetwork} =
  c_stop_network foreignNetwork
