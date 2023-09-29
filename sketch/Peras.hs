module Peras where

import qualified Data.Set as Set
import           Data.Set (Set)

--import           Control.Applicative
import           Control.Monad.Class.MonadSTM
import           Control.Concurrent.Class.MonadSTM.TVar
import           Control.Monad.Class.MonadAsync


data Chain payload = Genesis
                   | Block {
                       bHeader   :: BlockHeader,
                       bPayload  :: payload,
                       bPrevious :: Chain payload
                     }

data BlockHeader = BlockHeader {
       bhSlotNo   :: SlotNo,
       bhProducer :: ProducerId,
       bhPrevious :: Hash BlockHeader,
       bhVotes    :: Set (Hash Vote)
       -- Omitted: leader proof, signature
     }

newtype SlotNo = SlotNo Int
newtype ProducerId = ProducerId Int

data BlockBody = BlockBody

newtype Hash content = Hash Int

newtype VoteRoundNo = VoteRoundNo Int
  deriving Show

data Vote = Vote {
       vRoundNo  :: VoteRoundNo,
       vProducer :: ProducerId,
       vBlock    :: Hash BlockHeader
       -- Omitted: membership proof, signature
     }


validChain :: Chain payload -> Bool
validChain = undefined
  -- normal Praos validity
  -- vote conditions:
  -- * included votes can only refer to previous blocks on the chain
  --   within the vote candidate window (based on vote round number)
  -- * round number of included votes must be within the vote ballot window
  -- * and no vote duplicates/equivocations


data NodeState m = NodeState {
       currentChain :: TVar m (Chain BlockBody), -- C
       activeVotes  :: TVar m (Set Vote)         -- D
     }


-- A node's (delayed) view of a peer's state (c,d)
type PeerState m = NodeState m

peerStateSync :: NodeState m -> PeerState m -> m ()
peerStateSync = undefined
-- asynchronously synchronise the node state to the peer state with some delay

consensusNode :: (MonadSTM m, MonadAsync m)
              => NodeState m -> [PeerState m] -> m ()
consensusNode us peers =
    runConcurrently $
       () <$ votePropagation
          <* chainSelection
          <* votePruning
          <* blockForging
          <* blockVoting
  where
    votePropagation = undefined
      -- Take all peers d's and union them into our own d. In the case of
      -- duplicates, keep the ones already in our own d.

    chainSelection = undefined
      -- Upon changes to our view of other peer's chains c and our own d,
      -- evaluate weight of each chain c wrt to our own local d.
      -- Do the usual ouroboros chain selection: pick chain with biggest
      -- weight, preferring our own on ties, or abitrarily otherwise.

    votePruning = undefined
      -- On the round number advancing, prune our d to remove expired votes,
      -- based on a parameter that says the maximum number of rounds a vote is
      -- valid for.

    blockForging = undefined
      -- Wait for the start of each slot
      -- if we are slot leader, forge a block on C, extending to C',
      -- include all votes in D that are valid wrt C
      -- Where valid votes means votes that refer to blocks within C (within
      -- the validity window) and are not already contained in C.

    blockVoting = undefined
      -- On the start of each voting round...
      -- Check if we are in the committee for this round, and seenQuorum(C, D).
      -- If so, create a new vote and insert it into D.

shouldVote :: Chain payload -> Set Vote -> VoteRoundNo -> Bool
shouldVote c d r =
     quorumOnChainInRound c d (r-1)
  || {-   exists c. quorumOnChainInRound c Set.empty (r-c*cooldownRounds)
       && no quorum on c since round (r-c*cooldownRounds) -}
     -- equivalently: most recent quorum is at round (r-c*cooldownRounds)

-- | Number of voting rounds for a cooldown period
cooldownRounds :: Int
cooldownRounds = undefined

-- | Check if there was a quorum in the given round and whether the hash of the
-- block that the quorum is for is on our chain.
--
quorumOnChainInRound :: Chain payload -> Set Vote -> VoteRoundNo -> Bool
quorumOnChainInRound _c _d _r = undefined

