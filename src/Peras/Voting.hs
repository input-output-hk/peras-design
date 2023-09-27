{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}

-- | The /Voting layer/ of Peras algorithm.
module Peras.Voting where

import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word16, Word64)
import Peras.Block (PartyId)
import Peras.Chain (RoundNumber (..), Vote (..), isValid, makeVote)

data VoterConfig = VoterConfig
  { partyId :: PartyId
  , roundLength :: Word16
  , cooldownPeriod :: Word64
  , votingChainLength :: Word16
  , quorum :: Word64
  , voteBoost :: Double -- ?
  , weightBoost :: Double -- ?
  }
  deriving stock (Eq, Show)

data Message msg
  = VoteFor {round :: RoundNumber, message :: msg}
  | NewVote {vote :: Vote msg}
  deriving stock (Eq, Show)

data Decision msg
  = CastVote {vote :: Vote msg}
  | AcceptVote {vote :: Vote msg}
  | Noop
  deriving stock (Eq, Show)

data VoterState msg = VoterState
  { slot :: Word64
  , currentRound :: RoundNumber
  , votesReceived :: Map.Map RoundNumber (Set (Vote msg))
  -- ^ The votes received in each round for each particular chain.
  , seenQuorum :: RoundNumber
  -- ^ The last round at which we saw a quorum
  }

votingLayer :: VoterConfig -> VoterState msg -> Message msg -> Decision msg
votingLayer VoterConfig{partyId, cooldownPeriod} VoterState{slot, seenQuorum = RoundNumber lastSeenQuorum} = \case
  VoteFor{round, message}
    | (slot `isBeginningOf` round)
        && shouldVoteNow round
        && (partyId `isCommitteeMemberAt` round) ->
        let newVote = makeVote round partyId message
         in CastVote newVote
  NewVote vote
    | isValid vote -> AcceptVote vote
  _ -> Noop
 where
  isBeginningOf :: Word64 -> RoundNumber -> Bool
  isBeginningOf = undefined

  shouldVoteNow :: RoundNumber -> Bool
  shouldVoteNow (RoundNumber round) =
    -- either we are in a
    (round > 0 && lastSeenQuorum == round - 1)
      || (lastSeenQuorum `mod` cooldownPeriod == 0 && lastSeenQuorum `div` cooldownPeriod >= 1)

  isCommitteeMemberAt :: PartyId -> RoundNumber -> Bool
  isCommitteeMemberAt = undefined

class Monad m => VotingLayer m msg where
  -- | Diffuse given message across the network.
  diffuse :: msg -> m ()

  -- | Output message to upper layer.
  output :: msg -> m ()

decide :: (Ord msg, VotingLayer m (Message msg)) => VoterConfig -> VoterState msg -> Decision msg -> m (VoterState msg)
decide _ state@VoterState{votesReceived} = \case
  CastVote newVote@Vote{roundNumber} -> do
    let newState = state{votesReceived = Map.update (Just . Set.insert newVote) roundNumber votesReceived}
    diffuse (NewVote newVote)
    pure newState
  AcceptVote newVote@Vote{roundNumber} -> do
    let newState = state{votesReceived = Map.update (Just . Set.insert newVote) roundNumber votesReceived}
    output (NewVote newVote)
    pure newState
