module Peras.Prototype.NodeSpec where

import Prelude hiding (round)

import Control.Concurrent.Class.MonadSTM (MonadSTM (readTVarIO), atomically, writeTVar)
import Control.Monad.State (runStateT)
import Data.Default (def)
import Data.Function (on)
import Data.List (isSuffixOf, maximumBy)
import Data.Maybe (mapMaybe)
import Peras.Arbitraries (generateWith)
import Peras.Block (Block (certificate), Certificate (..))
import Peras.Crypto (hash)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Node (NodeState (..), initialNodeState, tick)
import Peras.Prototype.Types (PerasParams (..), PerasState (..), initialPerasState)
import Test.Hspec (Spec, describe, it, runIO, shouldBe)
import Test.QuickCheck (arbitrary)

import Control.Tracer (nullTracer)
import qualified Data.Map as Map (singleton)
import qualified Data.Set as Set (difference, fromList, size)

spec :: Spec
spec = do
  let params = def
      roundNumber = 430
      slotNumber = fromIntegral $ fromIntegral roundNumber * perasU params
      someChain = arbitrary `generateWith` 42
      someCertificate = (arbitrary `generateWith` 42){round = roundNumber - 1, blockRef = hash (head someChain)}
      payload = arbitrary `generateWith` 42
      boring = mkParty (arbitrary `generateWith` 42) [] []
      leaderOnly = mkParty (arbitrary `generateWith` 42) [slotNumber] []
      --    voterOnly = mkParty (arbitrary `generateWith` 42) [] [roundNumber]
      --    leaderAndVoter = mkParty (arbitrary `generateWith` 42) [slotNumber] [roundNumber]
      steadyState =
        initialPerasState
          { chainPref = someChain
          , chains = Set.fromList [[], someChain]
          , certs = Map.singleton someCertificate (slotNumber - 10)
          , certPrime = maximumBy (on compare round) $ someCertificate : mapMaybe certificate someChain
          , certStar = maximumBy (on compare round) $ mapMaybe certificate someChain
          }

  let check party properties =
        do
          nodeState <- runIO $ initialNodeState nullTracer party (slotNumber - 1) def
          runIO . atomically $ writeTVar (stateVar nodeState) steadyState
          perasState <- runIO . readTVarIO $ stateVar nodeState
          (result, nodeState') <- runIO $ runStateT (tick nullTracer payload) nodeState
          perasState' <- runIO . readTVarIO $ stateVar nodeState'
          it "Should not return an error." $ result `shouldBe` pure ()
          mapM_ (flip ($ perasState') perasState) properties

  let unchanged msg f = (it msg .) . on shouldBe f
      chainPrefUnchanged = unchanged "Preferred chain should not change." chainPref
      chainsUnchanged = unchanged "Chain set should not change." chains
      votesUnchanged = unchanged "Vote set should not change." votes
      certsUnchanged = unchanged "Certificate set should not change." certs
      certPrimeUnchanged = unchanged "Prime certificate should not change." certPrime
      certStarUnchanged = unchanged "Star certificate should not change." certStar
      oneMore msg f s' s = it msg $ Set.size (f s' `Set.difference` f s) `shouldBe` 1
      oneMoreChain = oneMore "Chain set should increase by one." chains
      --    oneMoreVote = oneMore "Vote set should increase by one." votes
      extendsOneBlock s' s = do
        it "Preferred chain should extend previous preferred chain." $
          (chainPref s `isSuffixOf` chainPref s') `shouldBe` True
        it "Preferred chain should increase by one block." $
          length (chainPref s') `shouldBe` length (chainPref s) + 1

  describe "Tick without slot leadership or committee membership" $
    check
      boring
      [ chainPrefUnchanged
      , chainsUnchanged
      , votesUnchanged
      , certsUnchanged
      , certPrimeUnchanged
      , certStarUnchanged
      ]

  describe "Tick with slot leadership but no committee membership" $
    check
      leaderOnly
      [ extendsOneBlock
      , oneMoreChain
      , votesUnchanged
      , certsUnchanged
      , certPrimeUnchanged
      , certStarUnchanged
      ]

-- FIXME: We need more sophisticated arbitraries for testing voting.
{-
  describe "Tick without slot leadership but with committee membership" $ do
    check voterOnly
      [ chainPrefUnchanged
      , chainsUnchanged
      , oneMoreVote
      , certsUnchanged
      , certPrimeUnchanged
      , certStarUnchanged
      ]

  describe "Tick with slot leadership and committee membership" $ do
    check leaderAndVoter
      [ extendsOneBlock
      , oneMoreChain
      , oneMoreVote
      , certsUnchanged
      , certPrimeUnchanged
      , certStarUnchanged
      ]
-}
