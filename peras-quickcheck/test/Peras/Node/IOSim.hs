{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Peras.Node.IOSim where

import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.Reader (ReaderT (runReaderT))
import Peras.Message (NodeId (..))
import Peras.NodeModel (Node (..), RunMonad, initialiseNodeEnv, runMonad)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM (..), monadic')

runPropInIOSim :: Testable a => (forall s. PropertyM (RunMonad (IOSim s)) a) -> Gen Property
runPropInIOSim p = do
  Capture eval <- capture
  let simTrace =
        runSimTrace $
          withNode
            >>= runReaderT (runMonad $ eval $ monadic' p)
      traceDump = map (\(t, s) -> show t <> " : " <> s) $ selectTraceEventsSayWithTime' simTrace
      logsOnError = counterexample ("trace:\n" <> unlines traceDump)
  case traceResult False simTrace of
    Right x ->
      pure $ logsOnError x
    Left ex ->
      pure $ counterexample (show ex) $ logsOnError $ property False

withNode :: IOSim s (Node (IOSim s))
withNode =
  initialiseNodeEnv >>= \(nodeThreadId, nodeProcess, nodeStake) ->
    pure $
      Node
        { nodeId = MkNodeId "N1"
        , nodeThreadId
        , nodeProcess
        , nodeStake
        }
