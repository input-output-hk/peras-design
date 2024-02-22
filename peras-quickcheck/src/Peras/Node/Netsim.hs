{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Node.Netsim where

import Control.Exception (IOException, finally, try)
import Control.Monad.Reader (ReaderT (..))
import qualified Data.Aeson as A
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LBS
import Data.Function ((&))
import Data.Functor ((<&>))
import Peras.IOSim.Message.Types (OutEnvelope)
import Peras.Message (NodeId (..))
import Peras.Node.Netsim.Rust (RustNode)
import qualified Peras.Node.Netsim.Rust as Rust
import Peras.NodeModel (Node (..), RunMonad, runMonad)
import Test.QuickCheck (Property, Testable, counterexample, ioProperty, property)
import Test.QuickCheck.Monadic (PropertyM, monadic)

runPropInNetSim :: Testable a => PropertyM (RunMonad IO) a -> Property
runPropInNetSim = monadic (ioProperty . runner)
 where
  runner :: RunMonad IO Property -> IO Property
  runner act =
    withNewNode $ \node ->
      runMonad act `runReaderT` node

withNewNode :: (Node IO -> IO Property) -> IO Property
withNewNode k = do
  node <- startNode (MkNodeId "N1") 1
  runTest node
    `finally` stopNode node
 where
  runTest node =
    try (k node)
      >>= \case
        Right v -> pure v
        Left (e :: IOException) ->
          pure $
            property False
              & counterexample ("Execution failed with error: " <> show e)

startNode :: NodeId -> Rational -> IO (Node IO)
startNode nodeId nodeStake = do
  rustNode <- Rust.startNode nodeId nodeStake
  pure $ mkNode rustNode
 where
  mkNode :: RustNode -> Node IO
  mkNode rustNode =
    Node
      { nodeId
      , sendMessage =
          -- FIXME: Should use CBOR?
          Rust.sendMessage rustNode . LBS.toStrict . A.encode
      , receiveMessage =
          -- FIXME: Should use CBOR?
          Rust.receiveMessage rustNode <&> unmarshall
      , stopNode = Rust.stopNode rustNode
      , nodeStake
      }

  unmarshall :: ByteString -> OutEnvelope
  unmarshall bs =
    either (error . (("Failed to deserialise received message (" <> show bs <> "): ") <>)) id . A.eitherDecode . LBS.fromStrict $ bs
