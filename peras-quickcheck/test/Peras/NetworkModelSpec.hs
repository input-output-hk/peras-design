{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Peras.NetworkModelSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, newTVarIO, readTVarIO, writeTVar)
import Control.Lens (uses, (&), (.~))
import Control.Monad (forM)
import Control.Monad.Class.MonadTime.SI (getCurrentTime)
import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.Random (mkStdGen, runRand)
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.State (StateT (..))
import Data.Default (def)
import Data.Functor (void)
import qualified Data.Map as Map
import Peras.Chain (Chain (..))
import Peras.IOSim.Network (createNetwork, randomTopology, startNodes, stepToIdle)
import Peras.IOSim.Network.Types (NetworkState, chainsSeen, currentStates, networkRandom)
import Peras.IOSim.Node (initializeNodes)
import Peras.IOSim.Protocol.Types (Protocol (PseudoPraos))
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.IOSim.Types (Votes)
import Peras.Message (NodeId)
import Peras.NetworkModel (Action (..), Network (..), RunMonad, Simulator (..), runMonad)
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyAction, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec =
  -- those tests are a bit slow...
  modifyMaxSuccess (const 30) $ prop "Chain progress" prop_chain_progress

prop_chain_progress :: Property
prop_chain_progress =
  within 50000000 $
    forAllDL chainProgress propNetworkModel

chainProgress :: DL Network ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \Network{nodeIds} -> do
    -- we need at least on run
    anyAction
    chains <- forM nodeIds (action . ObserveBestChain)
    void $ action $ ChainsHaveCommonPrefix chains

propNetworkModel :: Actions Network -> Property
propNetworkModel actions =
  property $
    runPropInIOSim $ do
      _ <- runActions actions
      assert True

runPropInIOSim :: Testable a => (forall s. PropertyM (RunMonad (IOSim s)) a) -> Gen Property
runPropInIOSim p = do
  Capture eval <- capture
  let simTrace =
        runSimTrace $
          mkPerasNetwork >>= runReaderT (runMonad $ eval $ monadic' p)
      traceDump = map (\(t, s) -> show t <> " : " <> s) $ selectTraceEventsSayWithTime' simTrace
      logsOnError = counterexample ("trace:\n" <> unlines traceDump)
  case traceResult False simTrace of
    Right x ->
      pure $ logsOnError x
    Left ex ->
      pure $ counterexample (show ex) $ logsOnError $ property False
 where
  gen = mkStdGen 42

  mkPerasNetwork :: IOSim s (Simulator (IOSim s))
  mkPerasNetwork = do
    let (topology, gen') = runRand (randomTopology parameters) gen
    now <- getCurrentTime
    let (states, gen'') = runRand (initializeNodes parameters now topology) gen'
    network <- createNetwork topology
    let initState :: NetworkState = def & networkRandom .~ gen'' & currentStates .~ states
    networkState <- newTVarIO initState
    runWithState networkState $ startNodes parameters protocol states network
    pure $
      Simulator
        { step = runWithState networkState $ stepToIdle parameters network
        , preferredChain = runWithState networkState . getPreferredChain
        , stop = pure ()
        }

getPreferredChain :: Monad m => NodeId -> StateT NetworkState m (Chain Votes)
getPreferredChain nodeId = chainsSeen `uses` (Map.! nodeId)

runWithState :: (Monad m, MonadSTM m) => TVar m NetworkState -> StateT NetworkState m a -> m a
runWithState stateVar act = do
  st <- readTVarIO stateVar
  (res, st') <- runStateT act st
  atomically $ writeTVar stateVar st'
  pure res

protocol :: Protocol
protocol = PseudoPraos defaultActiveSlotCoefficient

defaultActiveSlotCoefficient :: Double
defaultActiveSlotCoefficient = 0.05

parameters :: Parameters
parameters =
  Parameters
    { randomSeed = 12345
    , peerCount = 10
    , downstreamCount = 3
    , totalStake = Just 5000
    , maximumStake = 1000
    , endSlot = 1000
    , messageDelay = 0.35
    }
