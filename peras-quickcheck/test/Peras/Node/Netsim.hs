{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Node.Netsim where

import Control.Exception (IOException, throwIO, try)
import Control.Monad.Reader (ReaderT (..))
import Data.Function ((&))
import Peras.Message (NodeId (..))
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
  node <- startNode
  try (k node) >>= \case
    Right v -> pure v
    Left (e :: IOException) ->
      pure $
        property False
          & counterexample ("Execution failed with error: " <> show e)

startNode :: IO (Node IO)
startNode = pure node
 where
  node :: Node IO
  node =
    Node
      { nodeId = MkNodeId "N1"
      , sendMessage = const $ throwIO $ userError $ "not implemented"
      , receiveMessage = throwIO $ userError $ "not implemented"
      , nodeStake = 1
      }
