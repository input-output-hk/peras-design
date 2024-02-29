module Peras.Block where

import Numeric.Natural (Natural)
import Peras.Crypto (Hash, Hashable, LeadershipProof, Signature (bytes), VerificationKey)

import Peras.Crypto (Hash (..), Hashable (..))

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

instance Hashable Block where
  hash = \b -> Hash (bytes (signature b))
