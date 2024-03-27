{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Peras.Node.IOSim where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TQueue, atomically, newTQueueIO, readTQueue, writeTQueue)
import Control.Monad.Class.MonadFork (ThreadId, forkIO, killThread)
import Control.Monad.Class.MonadSay (MonadSay)
import Control.Monad.Class.MonadTime (diffUTCTime, getCurrentTime)
import Control.Monad.Class.MonadTimer (MonadDelay (..))
import Control.Monad.Class.MonadTimer.SI (MonadFork, MonadTime)
import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.Random (mkStdGen, runRand)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Tracer (Tracer, nullTracer)
import Data.Default (def)
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import qualified Data.Set as Set
import Peras.Event (Event)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope (Idle))
import Peras.IOSim.Node (initializeNode, stepNode)
import Peras.IOSim.Node.Types (PerasNode (..), StepResult (..), getStake)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Coin, simulationStart)
import Peras.Message (NodeId (..))
import Peras.NodeModel (Node (..), RunMonad, defaultActiveSlotCoefficient, runMonad)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM (..), monadic')

data NodeProcess m = NodeProcess (TQueue m InEnvelope) (TQueue m OutEnvelope)

runNode ::
  forall m a.
  MonadDelay m =>
  MonadSay m =>
  MonadSTM m =>
  MonadTime m =>
  PerasNode a =>
  Tracer m Event ->
  Protocol ->
  Coin ->
  a ->
  NodeProcess m ->
  m ()
runNode _tracer protocol' totalStake initial (NodeProcess incoming outgoing) =
  let loop :: a -> m ()
      loop state =
        do
          clock <- getCurrentTime
          let slot = floor . toRational $ clock `diffUTCTime` simulationStart
          input <- atomically $ readTQueue incoming
          let (StepResult{..}, state') = stepNode protocol' totalStake state slot clock (input :: InEnvelope)
          atomically $ mapM_ (writeTQueue outgoing) stepOutputs
          atomically $ writeTQueue outgoing Idle
          threadDelay . floor . (* 1_000_000) . toRational $ stepTime `diffUTCTime` clock
          loop state'
   in loop initial

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
  nodeProcess <- NodeProcess <$> newTQueueIO <*> newTQueueIO
  let (nodeState, _) = flip runRand gen $ initializeNode parameters (MkNodeId "N1") (Set.singleton $ MkNodeId "N2")
  -- FIXME: it's annoying to have threads running out of control
  threadId <- forkIO $ runNode nullTracer protocol (fromMaybe (maximumStake parameters) $ totalStake parameters) nodeState nodeProcess
  pure (threadId, nodeProcess, toInteger (getStake nodeState) % toInteger (fromMaybe (maximumStake parameters) $ totalStake parameters))

protocol :: Protocol
protocol = def{activeSlotCoefficient = defaultActiveSlotCoefficient}

parameters :: Parameters
parameters =
  Parameters
    { randomSeed = 12_345
    , peerCount = 1
    , downstreamCount = 3
    , totalStake = Just 1000
    , maximumStake = 1000
    , endSlot = 1000
    , messageLatency = 350_000
    , messageBandwidth = 250
    , experiment = Nothing
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
  initialiseNodeEnv >>= \(threadId, NodeProcess incoming outgoing, nodeStake) -> do
    pure $
      Node
        { nodeId = MkNodeId "N1"
        , sendMessage = atomically . writeTQueue incoming
        , receiveMessage = atomically $ readTQueue outgoing
        , nodeStake
        , stopNode = killThread threadId
        }
