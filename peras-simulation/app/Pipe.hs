{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (atomically, modifyTVar'),
 )
import Control.Monad (Monad ((>>=)), void, (=<<))
import Control.Monad.State (lift)
import Control.Tracer (nullTracer)
import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.Default (def)
import qualified Data.Map as Map (fromList)
import qualified Data.Set as Set (fromList)
import Data.Version (showVersion)
import Paths_peras_simulation (version)
import Peras.Conformance.Params (PerasParams (perasΔ))
import Peras.Conformance.Test.External (NodeRequest (..), NodeResponse (..))
import Peras.Prototype.BlockCreation (blockCreation)
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (mkCommitteeMember, mkSlotLeader)
import Peras.Prototype.Diffusion (Diffuser, allPendingChains, defaultDiffuser, diffuseChain, diffuseVote, popChainsAndVotes)
import Peras.Prototype.Environment (mkSimpleScenario)
import Peras.Prototype.Fetching (fetching)
import Peras.Prototype.Network (simulate, simulateNetwork)
import Peras.Prototype.Node (
  NodeState (..),
  defaultNodeState,
  tickNode,
 )
import Peras.Prototype.Trace (perasTracer)
import Peras.Prototype.Types (
  PerasState (certs, chains, votes),
  inRound,
 )
import Peras.Prototype.Visualizer (makeVisTracer)
import Peras.Prototype.Voting (voting)
import System.Exit (die)
import Prelude hiding (round)

main :: IO ()
main =
  let
    go node =
      (A.eitherDecode . LBS8.pack <$> getLine)
        >>= \case
          Right req -> do
            (res, node') <- handle node req
            case res of
              Stopped -> pure ()
              Failed e -> die e
              _ -> do
                LBS8.putStrLn $ A.encode res
                go node'
          Left e -> die $ show e
   in
    go =<< defaultNodeState

handle :: MonadSTM m => NodeState m -> NodeRequest -> m (NodeResponse, NodeState m)
handle node@MkNodeState{..} =
  \case
    Initialize{..} -> do
      atomically . modifyTVar' stateVar $
        \state ->
          state
            { chains = Set.fromList chainsSeen
            , votes = Set.fromList votesSeen
            , certs = Map.fromList $ (,slotNumber) <$> certsSeen
            }
      pure
        ( def
        , node
            { self = party
            , clock = slotNumber
            , protocol = parameters
            }
        )
    Tick ->
      pure (def, node{clock = clock + 1})
    Fetching{..} ->
      fetching nullTracer protocol self stateVar clock newChains newVotes
        >>= \case
          Right () -> pure (def, node)
          Left e -> pure (Failed $ show e, node)
    BlockCreation{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      let party = mkSlotLeader self clock isSlotLeader
      blockCreation nullTracer protocol party stateVar clock mempty (diffuseChain diffuserVar)
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    Voting{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      let party = mkCommitteeMember self protocol clock isCommitteeMember
      voting nullTracer protocol party stateVar clock (selectBlock nullTracer) (diffuseVote diffuserVar)
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    Step{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      tickNode nullTracer diffuserVar protocol self stateVar clock (inRound clock protocol) mempty newChains newVotes
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    Stop -> pure (Stopped, node)
