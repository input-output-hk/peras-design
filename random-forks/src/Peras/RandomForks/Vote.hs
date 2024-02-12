{-# LANGUAGE RecordWildCards #-}

module Peras.RandomForks.Vote (
  allVotes,
  refreshVotes,
  recordVote,
) where

import Peras.RandomForks.Chain (blocks)
import Peras.RandomForks.Types (Block (..), Chain (..), PeerName, Round, Slot, Vote (..))

import qualified Data.Set as S

allVotes ::
  [Chain] ->
  S.Set Vote ->
  S.Set Vote
allVotes chains dangling =
  let attached = foldMap (S.unions . fmap votes . blocks) chains
   in S.union attached dangling

refreshVotes ::
  S.Set Vote ->
  Chain ->
  (S.Set Vote, Chain)
refreshVotes votes' chain =
  let refreshVotes' Genesis = Genesis
      refreshVotes' Chain{..} =
        Chain
          (block{votes = votes block `S.union` S.filter ((== blockId block) . votedBlock) votes'})
          (refreshVotes' prev)
      chain' = refreshVotes' chain
   in (votes' `S.difference` foldMap votes (blocks chain'), chain')

recordVote ::
  Round ->
  PeerName ->
  (Slot, Slot) ->
  Chain ->
  Chain
recordVote votingRound voter (minSlot, maxSlot) chain =
  let recordVote' Genesis = Genesis
      recordVote' Chain{..} =
        if minSlot <= slot block && slot block <= maxSlot
          then
            let votedBlock = blockId block
             in Chain (block{votes = Vote{..} `S.insert` votes block}) prev
          else Chain block $ recordVote' prev
   in recordVote' chain
