module Peras.Block where

import Numeric.Natural (Natural)
import Peras.Crypto (Hash, Hashable, LeadershipProof, Signature (bytes), VerificationKey)

import Peras.Crypto (Hash (..), Hashable (..))

type PartyId = Natural

data Party = MkParty {id :: PartyId, vkey :: VerificationKey}
  deriving (Eq)

type Tx = ()

type Slot = Natural

data Certificate = Certificate {votingRoundNumber :: Natural}
  deriving (Eq)

data Block = Block
  { slotNumber :: Slot
  , creatorId :: PartyId
  , parentBlock :: Hash
  , certificate :: Maybe Certificate
  , leadershipProof :: LeadershipProof
  , signature :: Signature
  , bodyHash :: Hash
  }
  deriving (Eq)

data BlockBody = BlockBody {blockHash :: Hash, payload :: [Tx]}
  deriving (Eq)

instance Hashable Block where
  hash = \b -> Hash (bytes (signature b))
