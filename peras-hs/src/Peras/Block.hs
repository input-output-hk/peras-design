module Peras.Block where

import Numeric.Natural (Natural)
import Peras.Crypto (Hash, LeadershipProof, Signature, VerificationKey)

import Data.ByteString as BS

data PartyId = MkPartyId {vkey :: VerificationKey}

data Tx = Tx {tx :: ByteString}

type Slot = Natural

data Block t = Block
  { slotNumber :: Slot
  , creatorId :: PartyId
  , parentBlock :: Hash
  , includedVotes :: t
  , leadershipProof :: LeadershipProof
  , payload :: [Tx]
  , signature :: Signature
  }
