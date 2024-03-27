{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Peras.NetworkModelSpec where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, newTVarIO, readTVarIO, writeTVar)
import Control.Lens ((&), (.~))
import Control.Monad (forM)
import Control.Monad.IOSim (IOSim, runSimTrace, selectTraceEventsSayWithTime', traceResult)
import Control.Monad.Random (mkStdGen, runRand)
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.State (StateT (..), gets)
import Control.Tracer (nullTracer)
import Data.Default (def)
import Data.Functor (void)
import qualified Data.Map as Map
import Peras.Chain (Chain)
import Peras.IOSim.Network (createNetwork, randomTopology, stepNetwork)
import Peras.IOSim.Network.Types (NetworkState, chainsSeen, networkRandom)
import Peras.IOSim.Node (initializeNodes)
import Peras.Message (NodeId)
import Peras.Network.Netsim (runPropInNetSim)
import Peras.NetworkModel (Action (..), Network (..), RunMonad, Simulator (..), parameters, protocol, runMonad)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Gen, Property, Testable, counterexample, property, withMaxSuccess, within)
import Test.QuickCheck.DynamicLogic (DL, action, anyAction, anyActions_, forAllDL, getModelStateDL)
import Test.QuickCheck.Gen.Unsafe (Capture (..), capture)
import Test.QuickCheck.Monadic (PropertyM, assert, monadic')
import Test.QuickCheck.StateModel (Actions, runActions)

spec :: Spec
spec = do
  -- those tests are a bit slow...
  modifyMaxSuccess (const 50) $
    describe "IOSim Network" $
      prop "Chain progress" (prop_chain_progress propIOSimNetwork)

  describe "Netsim Network" $
    prop "Chain progress" $
      withMaxSuccess 20 $
        prop_chain_progress propNetsimNetwork

prop_chain_progress :: (Actions Network -> Property) -> Property
prop_chain_progress runProp =
  within 50_000_000 $
    forAllDL chainProgress runProp

chainProgress :: DL Network ()
chainProgress = do
  anyActions_
  getModelStateDL >>= \Network{nodeIds} -> do
    -- we need at least on run
    anyAction
    chains <- forM nodeIds (action . ObserveBestChain)
    void $ action $ ChainsHaveCommonPrefix chains

propIOSimNetwork :: Actions Network -> Property
propIOSimNetwork actions =
  property $ runPropInIOSim $ do
    _ <- runActions actions
    assert True

propNetsimNetwork :: Actions Network -> Property
propNetsimNetwork actions =
  property $ runPropInNetSim $ do
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
    let (states, gen'') = runRand (initializeNodes parameters topology) gen'
    networkState <- newTVarIO $ createNetwork parameters topology states $ def & networkRandom .~ gen''
    pure $
      Simulator
        { step = runWithState networkState . StateT $ fmap ((),) . stepNetwork False nullTracer protocol
        , preferredChain = runWithState networkState . getPreferredChain
        , stop = pure ()
        }

getPreferredChain :: Monad m => NodeId -> StateT NetworkState m Chain
getPreferredChain nodeId = gets $ (Map.! nodeId) . chainsSeen

runWithState :: (Monad m, MonadSTM m) => TVar m NetworkState -> StateT NetworkState m a -> m a
runWithState stateVar act = do
  st <- readTVarIO stateVar
  (res, st') <- runStateT act st
  atomically $ writeTVar stateVar st'
  pure res
