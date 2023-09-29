{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

-- | The Nakamoto layer of the Peras protocol.
module Peras.Nakamoto where

import Data.Map (Map)
import Data.Set (Set)
import Data.Word (Word64)
import Peras.Block (Block (..), PartyId, isValidBlock)
import Peras.Chain (Vote)
import Peras.Message (Message (..))

data ConsensusConfig = ConsensusConfig
  { partyId :: PartyId
  , roundLength :: Word64
  , cooldownPeriod :: Word64
  }
  deriving stock (Eq, Show)

-- | Compute the weight of a (tip of) a chain w.r.t to a set of
-- pending votes.
--
-- The weight of a (valid) chain C is computed w.r.t. to a set D of
-- C-dangling votes. A C-dangling vote votes for a block in C, is not
-- already referenced by blocks in C, and is not an equivocation of a
-- vote referenced by blocks in C.
chainWeight :: ConsensusConfig -> Block -> Set (Vote Block) -> Word64
chainWeight ConsensusConfig{roundLength} Block{blockHeight, slotNumber} pendingVotes =
  let chainWeight = blockHeight
      currentRound = slotNumber `div` roundLength
   in undefined

data ConsensusState = ConsensusState
  { currentChain :: Block
  , seenChains :: Set Block
  , votesReceived :: Map Word64 (Map Block (Set (Vote Block)))
  }
  deriving stock (Eq, Show)

data Decision
  = Tally (Vote Block)
  | Seen Block
  deriving stock (Eq, Show)

nakamotoLayer :: ConsensusConfig -> ConsensusState -> Message Block -> Decision
nakamotoLayer config state = \case
  NewVote vote -> Tally vote
  NewChain block | isValidBlock block -> Seen block
  Slot s ->
