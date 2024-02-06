-- | The Nakamoto layer of the Peras protocol.
module Peras.Nakamoto where

open import Agda.Builtin.Word
open import Level
open import Data.Tree.AVL.Sets renaming (⟨Set⟩ to set)
open import Data.Tree.AVL.Map
open import Relation.Binary

open import Peras.Block
open import Peras.Chain

record ConsensusConfig : Set where
  constructor mkConsensusConfig
  field partyId : PartyId
        roundLength : Word64
        cooldownPeriod : Word64

-- | Compute the weight of a (tip of) a chain w.r.t to a set of
-- pending votes.
--
-- The weight of a (valid) chain C is computed w.r.t. to a set D of
-- C-dangling votes. A C-dangling vote votes for a block in C, is not
-- already referenced by blocks in C, and is not an equivocation of a
-- vote referenced by blocks in C.

postulate chainWeight : ConsensusConfig -> Block -> set VoteBlockO -> Word64
{-
chainWeight ConsensusConfig{roundLength} Block{blockHeight, slotNumber} pendingVotes =
  let chainWeight = blockHeight
      currentRound = slotNumber `div` roundLength
   in undefined
-}

postulate
  wEq : Relation.Binary.Rel Word64 zero
  wLt : Relation.Binary.Rel Word64 zero
  wIs : Relation.Binary.IsStrictTotalOrder wEq wLt

WordO : StrictTotalOrder zero zero zero
WordO = record {
  Carrier            = Word64 ;
  _≈_                = wEq ;
  _<_                = wLt ;
  isStrictTotalOrder = wIs }


record ConsensusState : Set where
  constructor consensusState
  field currentChain  : Block
        seenChains    : set BlockO
        votesReceived : Map WordO (Map BlockO (set VoteBlockO))

data Decision : Set where
  Tally : Vote Block → Decision
  Seen  : Block → Decision

{-
nakamotoLayer :: ConsensusConfig -> ConsensusState -> Message Block -> Decision
nakamotoLayer config state = \case
  NewVote vote -> Tally vote
  NewChain block | isValidBlock block -> Seen block
  Slot s ->
-}
