{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | FFI interface to a node in Rust
module Peras.Node.Netsim.Rust (
  RustNode,
  startNode,
  stopNode,
)
where

import Foreign (Ptr)
import Foreign.C (CString, withCString)
import Peras.Message (NodeId (..))

newtype RustNode = RustNode {foreignNode :: Ptr ForeignNode}

data ForeignNode

foreign import capi unsafe "peras.h start_node" c_start_node :: CString -> Double -> IO (Ptr ForeignNode)

foreign import capi unsafe "peras.h stop_node" c_stop_node :: Ptr ForeignNode -> IO ()

-- | Start a `RustNode` with given id and amount of stake.
startNode :: NodeId -> Rational -> IO RustNode
startNode MkNodeId{nodeId} stake =
  withCString nodeId $ \cstr ->
    RustNode <$> c_start_node cstr (fromRational stake)

-- | Stop given `RustNode`.
stopNode :: RustNode -> IO ()
stopNode RustNode{foreignNode} =
  c_stop_node foreignNode
