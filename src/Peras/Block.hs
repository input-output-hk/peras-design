{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Peras.Block where

import Data.Word (Word64)
import Peras.Crypto (Hash, LeadershipProof, Signature, VerificationKey)
import Data.Set (Set)
import Data.ByteString (ByteString)

data Block = Block
  { slotNumber :: Word64
  , creatorId :: PartyId
  , parentBlock :: Hash
  , includedVotes :: Set Hash
  , leadershipProof :: LeadershipProof
  , payload :: [Tx]
  , signature :: Signature
  }
 deriving stock (Eq, Show)

newtype Tx = Tx { tx :: ByteString }
  deriving newtype (Eq, Show)

newtype PartyId = PartyId {vkey :: VerificationKey}
  deriving newtype (Eq, Show, Ord)
