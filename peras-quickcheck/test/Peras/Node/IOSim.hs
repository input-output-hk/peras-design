{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}

module Peras.Node.IOSim where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically, newTQueueIO, readTQueue, writeTQueue)
import Control.Lens ((^.))
import Control.Monad.Class.MonadFork (ThreadId, forkIO, killThread)
import Control.Monad.Class.MonadSay (MonadSay)
import Control.Monad.Class.MonadTime (getCurrentTime)
import Control.Monad.Class.MonadTimer.SI (MonadDelay, MonadFork, MonadTime)
import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.Random (mkStdGen, runRand)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.Default (def)
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import qualified Data.Set as Set
import Peras.IOSim.Node (NodeProcess (..), initializeNode, runNode)
import Peras.IOSim.Node.Types (stake)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.Message (NodeId (..))
import Peras.NodeModel (Node (..), RunMonad, defaultActiveSlotCoefficient, runMonad)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM (..), monadic')

initialiseNodeEnv ::
  ( MonadSTM m
  , MonadDelay m
  , MonadSay m
  , MonadTime m
  , MonadFork m
  ) =>
  m (ThreadId m, NodeProcess m, Rational)
initialiseNodeEnv = do
  let gen = mkStdGen 42
  now <- getCurrentTime
  nodeProcess <- NodeProcess <$> newTQueueIO <*> newTQueueIO
  let (nodeState, _) = flip runRand gen $ initializeNode parameters now (MkNodeId "N1") (Set.singleton $ MkNodeId "N2")
  -- FIXME: it's annoying to have threads running out of control
  threadId <- forkIO $ runNode protocol (fromMaybe (maximumStake parameters) $ totalStake parameters) nodeState nodeProcess
  pure (threadId, nodeProcess, toInteger (nodeState ^. stake) % toInteger (fromMaybe (maximumStake parameters) $ totalStake parameters))

protocol :: Protocol
protocol = def{activeSlotCoefficient = defaultActiveSlotCoefficient}

parameters :: Parameters
parameters =
  Parameters
    { randomSeed = 12345
    , peerCount = 1
    , downstreamCount = 3
    , totalStake = Just 1000
    , maximumStake = 1000
    , endSlot = 1000
    , messageDelay = 350_000
    }

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
  initialiseNodeEnv >>= \(threadId, NodeProcess{incoming, outgoing}, nodeStake) -> do
    pure $
      Node
        { nodeId = MkNodeId "N1"
        , sendMessage = atomically . writeTQueue incoming
        , receiveMessage = atomically $ readTQueue outgoing
        , nodeStake
        , stopNode = killThread threadId
        }
