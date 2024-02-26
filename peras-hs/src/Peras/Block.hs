module Peras.Block where

import Numeric.Natural (Natural)
import Peras.Crypto (Hash, LeadershipProof, Signature, VerificationKey)

type PartyId = Natural

data Party = MkParty {id :: PartyId, vkey :: VerificationKey}
  deriving (Eq)

type Tx = ()

type Slot = Natural

data Block = Block
  { slotNumber :: Slot
  , creatorId :: PartyId
  , parentBlock :: Hash
  , includedVotes :: [Hash]
  , leadershipProof :: LeadershipProof
  , payload :: [Tx]
  , signature :: Signature
  }
  deriving (Eq)
