{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (atomically, modifyTVar'),
 )
import Control.Monad (Monad ((>>=)), void, (=<<))
import Control.Monad.IO.Class
import Control.Monad.State (lift)
import Control.Tracer (Tracer, nullTracer, traceWith)
import qualified Data.Aeson as A
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.Default (def)
import qualified Data.Map as Map (fromList)
import qualified Data.Set as Set (fromList)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T
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
  initialNodeState,
  tickNode,
 )
import Peras.Prototype.Trace (PerasLog (Protocol), perasTracer)
import Peras.Prototype.Types (
  PerasState (certs, chains, votes),
  inRound,
 )
import Peras.Prototype.Visualizer (makeVisTracer)
import Peras.Prototype.Voting (voting)
import System.Exit (die)
import System.IO
import Prelude hiding (getLine, round)

main :: IO ()
main =
  do
    hSetBuffering stdin LineBuffering
    hSetBuffering stdout LineBuffering
    let
      go node =
        do
          -- Verified that this reads UTF-8.
          (A.eitherDecode . LBS.fromStrict <$> BS8.getLine)
            >>= \case
              Right req -> do
                LBS8.hPutStrLn stderr $ A.encode req
                (res, node') <- handle perasTracer node req
                LBS8.hPutStrLn stderr $ A.encode res
                LBS8.hPutStrLn stderr mempty
                case res of
                  Stopped -> pure ()
                  Failed e -> die e
                  _ -> do
                    -- Verified that this writes UTF-8.
                    LBS8.putStrLn $ A.encode res
                    go node'
              Left e -> die $ show e
     in
      go =<< defaultNodeState

handle :: MonadIO m => MonadSTM m => Tracer m PerasLog -> NodeState m -> NodeRequest -> m (NodeResponse, NodeState m)
handle tracer node@MkNodeState{..} =
  \case
    Initialize{..} -> do
      node <- initialNodeState tracer party slotNumber parameters
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
        )
    Tick ->
      pure (def, node{clock = clock + 1})
    Fetching{..} ->
      fetching tracer protocol self stateVar clock newChains newVotes
        >>= \case
          Right () -> pure (def, node)
          Left e -> pure (Failed $ show e, node)
    BlockCreation{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      let party = mkSlotLeader self clock isSlotLeader
      blockCreation tracer protocol party stateVar clock mempty (diffuseChain diffuserVar)
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    Voting{..} -> do
      void $ popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
      let party = mkCommitteeMember self protocol clock isCommitteeMember
      voting tracer protocol party stateVar clock (selectBlock tracer) (diffuseVote diffuserVar)
        >>= \case
          Right () -> (,node) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node)
    NewSlot{..} -> do
      let clock' = clock + 1
      liftIO $ hPrint stderr (clock, clock')
      void $ popChainsAndVotes diffuserVar (clock' + fromIntegral (perasΔ protocol) + 1)
      tickNode tracer diffuserVar protocol self stateVar clock' (inRound clock' protocol) mempty newChains newVotes
        >>= \case
          Right () -> (,node{clock = clock'}) . uncurry NodeResponse <$> popChainsAndVotes diffuserVar (clock' + fromIntegral (perasΔ protocol) + 1)
          Left e -> pure (Failed $ show e, node{clock = clock'})
    Stop -> pure (Stopped, node)
