{-# LANGUAGE NamedFieldPuns #-}

module Peras.Abstract.Protocol.NodeSpec where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), atomically, writeTVar)
import Control.Monad.State (MonadIO (liftIO), execStateT)
import Peras.Abstract.Protocol.Crypto (mkParty)
import Peras.Abstract.Protocol.Node (NodeState (stateVar), initialNodeState, tick)
import Peras.Abstract.Protocol.Types (PerasParams (..), PerasState (..), defaultParams, initialPerasState)
import Peras.Arbitraries (generateWith)
import Peras.Block (Certificate (..))
import Peras.Crypto (hash)
import Test.Hspec (Spec, it, shouldBe)
import Test.QuickCheck (arbitrary)

import qualified Data.Set as Set (size)

spec :: Spec
spec = do
  let params = defaultParams
      roundNumber = 430
      slotNumber = fromIntegral $ fromIntegral roundNumber * perasU params
      someChain = arbitrary `generateWith` 42
      someCertificate = (arbitrary `generateWith` 42){round = roundNumber - 1, blockRef = hash (head someChain)}
      payload = arbitrary `generateWith` 42
      boring = mkParty (arbitrary `generateWith` 42) [] []
      leaderOnly = mkParty (arbitrary `generateWith` 42) [slotNumber] []
      voterOnly = mkParty (arbitrary `generateWith` 42) [] [roundNumber]
      leaderAndVoter = mkParty (arbitrary `generateWith` 42) [slotNumber] [roundNumber]
      steadyState =
        initialPerasState
          { chainPref = someChain
          , certPrime = someCertificate
          }
  it "Tick without slot leadership or committee membership" $ do
    nodeState <- initialNodeState boring (slotNumber - 1)
    liftIO . atomically $ writeTVar (stateVar nodeState) steadyState
    nodeState' <- liftIO $ execStateT (tick payload) nodeState
    perasState <- readTVarIO $ stateVar nodeState
    perasState' <- readTVarIO $ stateVar nodeState'
    chainPref perasState' `shouldBe` chainPref perasState
    chains perasState' `shouldBe` chains perasState
    votes perasState' `shouldBe` votes perasState
    certs perasState' `shouldBe` certs perasState
    certPrime perasState' `shouldBe` certPrime perasState
    certStar perasState' `shouldBe` certStar perasState

  it "Tick with slot leadership but no committee membership" $ do
    nodeState <- initialNodeState leaderOnly (slotNumber - 1)
    liftIO . atomically $ writeTVar (stateVar nodeState) steadyState
    nodeState' <- liftIO $ execStateT (tick payload) nodeState
    perasState <- readTVarIO $ stateVar nodeState
    perasState' <- readTVarIO $ stateVar nodeState'
    chainPref perasState' `shouldBe` chainPref perasState
    Set.size (chains perasState') `shouldBe` Set.size (chains perasState) + 1
    votes perasState' `shouldBe` votes perasState
    certs perasState' `shouldBe` certs perasState
    certPrime perasState' `shouldBe` certPrime perasState
    certStar perasState' `shouldBe` certStar perasState

  it "Tick without slot leadership but with committee membership" $ do
    nodeState <- initialNodeState voterOnly (slotNumber - 1)
    liftIO . atomically $ writeTVar (stateVar nodeState) steadyState
    nodeState' <- liftIO $ execStateT (tick payload) nodeState
    perasState <- readTVarIO $ stateVar nodeState
    perasState' <- readTVarIO $ stateVar nodeState'
    chainPref perasState' `shouldBe` chainPref perasState
    chains perasState' `shouldBe` chains perasState
    Set.size (votes perasState') `shouldBe` Set.size (votes perasState) + 1
    certs perasState' `shouldBe` certs perasState
    certPrime perasState' `shouldBe` certPrime perasState
    certStar perasState' `shouldBe` certStar perasState

  it "Tick with slot leadership and committee membership" $ do
    nodeState <- initialNodeState leaderAndVoter (slotNumber - 1)
    liftIO . atomically $ writeTVar (stateVar nodeState) steadyState
    nodeState' <- liftIO $ execStateT (tick payload) nodeState
    perasState <- readTVarIO $ stateVar nodeState
    perasState' <- readTVarIO $ stateVar nodeState'
    chainPref perasState' `shouldBe` chainPref perasState
    (Set.size $ chains perasState', Set.size $ votes perasState') `shouldBe` (Set.size (chains perasState) + 1, Set.size (votes perasState) + 1)
    certs perasState' `shouldBe` certs perasState
    certPrime perasState' `shouldBe` certPrime perasState
    certStar perasState' `shouldBe` certStar perasState
