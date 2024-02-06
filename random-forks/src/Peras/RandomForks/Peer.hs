{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Peras.RandomForks.Peer (
  Peers(..)
, PeerState(..)
, nextSlot
, randomPeers
) where

import Data.List (delete)
import Data.Maybe (fromMaybe)
import Peras.RandomForks.Chain (Chain (Genesis), Message(..), chainLength, extendChain, mkBlock)
import Peras.RandomForks.Protocol (Protocol(..), Parameters(..), isCommitteeMember, isFirstSlotInRound, isSlotLeader)
import Peras.RandomForks.Types (Currency, PeerName(..), Slot)
import System.Random.Stateful (StatefulGen, UniformRange(uniformRM))

import qualified Data.Map.Strict as M
import qualified Data.Set as S

newtype Peers = Peers {getPeers :: M.Map PeerName PeerState}
  deriving (Eq, Ord, Read, Show)

data PeerState =
  PeerState
  {
    currency :: Currency
  , vrfOutput :: Double
  , slotLeader :: Bool
  , committeeMember :: Bool
  , upstream :: S.Set PeerName
  , downstream :: S.Set PeerName
  , preferredChain :: Chain
  , pendingMessages :: [Message]
  }
    deriving (Eq, Ord, Read, Show)

randomPeers
  :: StatefulGen g m
  => g
  -> Parameters
  -> Protocol
  -> m Peers
randomPeers gen Parameters{..} protocol =
  do
    let
      peerNames = PeerName . ("Peer " <>) . show <$> [1..peerCount]
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
nextSlot gen protocol slot name state@PeerState{..} =
  do
    vrfOutput' <- uniformRM (0, 1) gen
    slotLeader' <- isSlotLeader gen protocol currency
    let
      chains = preferredChain : (messageChain <$> pendingMessages)
      longest = filter ((>= maximum (chainLength <$> chains)) . chainLength) chains
    preferredChainBeforeNow <- (longest !!) <$> uniformRM (0, length longest - 1) gen
    preferredChain' <-
      if slotLeader'
        then (`extendChain` preferredChainBeforeNow) <$> mkBlock gen name slot
        else pure preferredChainBeforeNow
    let
      newMessages =
        if slotLeader'
          then Message slot preferredChain' <$> S.toList downstream
          else mempty
    committeeMember' <-
      if isFirstSlotInRound protocol slot
        then isCommitteeMember gen protocol currency
        else pure committeeMember
    let
      -- FIXME: Use lenses.
      newState =
        state
        {
          vrfOutput = vrfOutput'
        , slotLeader = slotLeader'
        , committeeMember = committeeMember'
        , preferredChain = preferredChain'
        , pendingMessages = mempty
        }
    pure (newState, newMessages)
