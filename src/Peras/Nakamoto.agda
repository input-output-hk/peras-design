-- | The Nakamoto layer of the Peras protocol.
module Peras.Nakamoto where
{-# FOREIGN AGDA2HS
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
#-}

{-# FOREIGN AGDA2HS
import Data.Word (Word64)
import Data.Map (Map)
import qualified Data.Set as S (Set)
type SET = S.Set
#-}
-- import Peras.Block (Block (..), PartyId, isValidBlock)
-- import Peras.Chain (Vote)
-- import Peras.Message (Message (..))

open import Agda.Builtin.Word

open import Peras.Block
open import Peras.Chain

postulate Map : Set → Set → Set

record ConsensusConfig : Set where
  field partyId : PartyId
        roundLength : Word64
        cooldownPeriod : Word64
open ConsensusConfig public
{-# COMPILE AGDA2HS ConsensusConfig deriving (Eq, Show) #-}
-- stock deriving strategy not supported

-- | Compute the weight of a (tip of) a chain w.r.t to a set of
-- pending votes.
--
-- The weight of a (valid) chain C is computed w.r.t. to a set D of
-- C-dangling votes. A C-dangling vote votes for a block in C, is not
-- already referenced by blocks in C, and is not an equivocation of a
-- vote referenced by blocks in C.

postulate chainWeight : ConsensusConfig -> Block -> SET (Vote Block) -> Word64
{-
chainWeight ConsensusConfig{roundLength} Block{blockHeight, slotNumber} pendingVotes =
  let chainWeight = blockHeight
      currentRound = slotNumber `div` roundLength
   in undefined
-}

record ConsensusState : Set where
  field currentChain  : Block
        seenChains    : SET Block
        votesReceived : Map Word64 (Map Block (SET (Vote Block)))
open ConsensusState public
{-# COMPILE AGDA2HS ConsensusState deriving (Eq, Show) #-}
-- stock deriving strategy not supported

data Decision : Set where
  Tally : Vote Block → Decision
  Seen  : Block → Decision
{-# COMPILE AGDA2HS Decision deriving (Eq, Show) #-}
-- stock deriving strategy not supported

{-
nakamotoLayer :: ConsensusConfig -> ConsensusState -> Message Block -> Decision
nakamotoLayer config state = \case
  NewVote vote -> Tally vote
  NewChain block | isValidBlock block -> Seen block
  Slot s ->
-}
