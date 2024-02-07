{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.RandomForks.Peer (
  nextSlot
, randomPeers
) where

import Data.List (delete)
import Data.Maybe (fromMaybe)
import Peras.RandomForks.Chain (chainWeight, extendChain, mkBlock)
import Peras.RandomForks.Protocol (isCommitteeMember, isFirstSlotInRound, isSlotLeader)
import Peras.RandomForks.Types (Chain (Genesis), Message(..), Parameters(..), PeerName(..), PeerState(..), Peers(..), Protocol(..), Slot)
import Peras.RandomForks.Vote (allVotes, recordVote, refreshVotes)
import System.Random.Stateful (StatefulGen, UniformRange(uniformRM))

import qualified Peras.RandomForks.Types as Protocol (Protocol(votingBoost))
import qualified Data.Map.Strict as M
import qualified Data.Set as S

randomPeers
  :: StatefulGen g m
  => g
  -> Parameters
  -> Protocol
  -> m Peers
randomPeers gen Parameters{..} protocol =
  do
    let
      peerNames = PeerName . ("P" <>) . show <$> [1..peerCount]
      randomSubset 0 _ = pure mempty
      randomSubset n items =
        do
          item <- (items !!) <$> uniformRM (0, length items - 1) gen
          S.insert item <$> randomSubset (n - 1) (delete item items)
    downstreams <- M.fromList <$> mapM (\name -> (name, ) <$> randomSubset downstreamCount (delete name peerNames)) peerNames
    let
      upstreams = M.fromListWith (<>) . concatMap (\(name, names) -> (, S.singleton name) <$> S.toList names) $ M.toList downstreams
      randomPeer name =
        do
          currency <- uniformRM (1, maximumCurrency) gen
          vrfOutput <- uniformRM (0, 1) gen
          slotLeader <- isSlotLeader gen protocol currency
          committeeMember <- isCommitteeMember gen protocol currency
          let upstream = fromMaybe mempty $ M.lookup name upstreams
              downstream = fromMaybe mempty $ M.lookup name downstreams
              preferredChain = Genesis
              pendingMessages = mempty
              danglingVotes = mempty
          pure PeerState{..}
    Peers . M.fromList <$> mapM (\name -> (name, ) <$> randomPeer name) peerNames

nextSlot
  :: StatefulGen g m
  => g
  -> Protocol
  -> Slot
  -> PeerName
  -> PeerState
  -> m (PeerState, [Message])
nextSlot gen protocol@Protocol{roundDuration, votingWindow} slot name state@PeerState{..} =
  do
    vrfOutput' <- uniformRM (0, 1) gen
    slotLeader' <- isSlotLeader gen protocol currency
    committeeMember' <-
      if isFirstSlotInRound protocol slot
        then isCommitteeMember gen protocol currency
        else pure committeeMember
    let
      chainWeight' = chainWeight $ Protocol.votingBoost protocol
      chains = preferredChain : fmap messageChain pendingMessages
      votes' = allVotes chains danglingVotes
      longest = filter ((>= maximum (chainWeight' <$> chains)) . chainWeight') chains
    preferredChainBeforeNow <- (longest !!) <$> uniformRM (0, length longest - 1) gen
    preferredChain' <-
      if slotLeader'
        then (`extendChain` preferredChainBeforeNow) <$> mkBlock gen name slot
        else pure preferredChainBeforeNow
    let
      (danglingVotes', preferredChain'') = refreshVotes votes' preferredChain'
      newMessages =
        if slotLeader'
          then (\destination -> Message slot destination preferredChain' danglingVotes) <$> S.toList downstream
          else mempty
    let
      -- FIXME: Use lenses.
      newState =
        state
        {
          vrfOutput = vrfOutput'
        , slotLeader = slotLeader'
        , committeeMember = committeeMember'
        , preferredChain = if committeeMember' && slot `mod` roundDuration == 0
                             then recordVote (slot `div` roundDuration) name (slot - snd votingWindow, slot - fst votingWindow) preferredChain''
                             else preferredChain''
        , danglingVotes = danglingVotes'
        , pendingMessages = mempty
        }
    pure (newState, newMessages)
