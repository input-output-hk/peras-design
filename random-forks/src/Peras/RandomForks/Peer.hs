{-# LANGUAGE NamedFieldPuns #-}
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
import System.Random (randomRIO)

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
  :: Parameters
  -> Protocol
  -> IO Peers
randomPeers Parameters{..} protocol =
  do
    let
      peerNames = PeerName . ("Peer " <>) . show <$> [1..peerCount]
      randomSubset 0 _ = pure mempty
      randomSubset n items =
        do
          item <- (items !!) <$> randomRIO (0, length items - 1)
          S.insert item <$> randomSubset (n - 1) (delete item items)
    downstreams <- M.fromList <$> mapM (\name -> (name, ) <$> randomSubset downstreamCount (delete name peerNames)) peerNames
    let
      upstreams = M.fromListWith (<>) . concatMap (\(name, names) -> (, S.singleton name) <$> S.toList names) $ M.toList downstreams
      randomPeer name =
        do
          currency <- randomRIO (1, maximumCurrency)
          vrfOutput <- randomRIO (0, 1)
          slotLeader <- isSlotLeader protocol currency
          committeeMember <- isCommitteeMember protocol currency
          let upstream = fromMaybe mempty $ M.lookup name upstreams
              downstream = fromMaybe mempty $ M.lookup name downstreams
              preferredChain = Genesis
              pendingMessages = mempty
          pure PeerState{..}
    Peers . M.fromList <$> mapM (\name -> (name, ) <$> randomPeer name) peerNames

nextSlot
  :: Protocol
  -> Slot
  -> PeerName
  -> PeerState
  -> IO (PeerState, [Message])
nextSlot protocol slot name state@PeerState{..} =
  do
    vrfOutput' <- randomRIO (0, 1)
    slotLeader' <- isSlotLeader protocol currency
    let
      chains = preferredChain : (messageChain <$> pendingMessages)
      longest = filter ((>= maximum (chainLength <$> chains)) . chainLength) chains
    preferredChainBeforeNow <- (longest !!) <$> randomRIO (0, length longest - 1)
    preferredChain' <-
      if slotLeader'
        then (`extendChain` preferredChainBeforeNow) <$> mkBlock name slot
        else pure preferredChainBeforeNow
    let
      newMessages =
        if slotLeader'
          then Message slot preferredChain' <$> S.toList downstream
          else mempty
    committeeMember' <-
      if isFirstSlotInRound protocol slot
        then isCommitteeMember protocol currency
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
