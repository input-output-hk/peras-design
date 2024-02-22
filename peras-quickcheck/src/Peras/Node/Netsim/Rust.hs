{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | FFI interface to a node in Rust
module Peras.Node.Netsim.Rust (
  RustNode,
  startNode,
  stopNode,
  sendMessage,
  receiveMessage,
)
where

import Control.Exception (bracket)
import Data.Bits ((.<<.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Internal (toForeignPtr0)
import Foreign (Ptr, Word8, free, mallocBytes, peekArray, withForeignPtr)
import Foreign.C (CString, withCString)
import Peras.Message (NodeId (..))

newtype RustNode = RustNode {foreignNode :: Ptr PerasNode}

data PerasNode

foreign import capi unsafe "peras.h start_node" c_start_node :: CString -> Double -> IO (Ptr PerasNode)

foreign import capi unsafe "peras.h stop_node" c_stop_node :: Ptr PerasNode -> IO ()

foreign import capi unsafe "peras.h send_message" c_send_message :: Ptr PerasNode -> Ptr Word8 -> Int -> IO ()

foreign import capi unsafe "peras.h receive_message" c_receive_message :: Ptr PerasNode -> Ptr Word8 -> Int -> IO Int

-- | Start a `RustNode` with given id and amount of stake.
startNode :: NodeId -> Rational -> IO RustNode
startNode MkNodeId{nodeId} stake =
  withCString nodeId $ \cstr ->
    RustNode <$> c_start_node cstr (fromRational stake)

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
bufferSize = 1 .<<. 12

receiveMessage :: RustNode -> IO ByteString
receiveMessage RustNode{foreignNode} = do
  bracket (mallocBytes bufferSize) free $ \ptr -> do
    len <- c_receive_message foreignNode ptr bufferSize
    BS.pack <$> peekArray len ptr
