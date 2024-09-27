{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Peras.Block where

import Peras.Crypto (Hash (MkHash), Hashable (hash), LeadershipProof, Signature (bytesS), VerificationKey, emptyBS)
import Peras.Numbering (RoundNumber, SlotNumber)

import GHC.Generics (Generic)
import Peras.Crypto (Hash (..), Hashable (..))
import Prelude hiding (round)

-- Use `Integer` for compatibility with `MAlonzo`.
type PartyId = Integer

data Party = MkParty {pid :: PartyId, pkey :: VerificationKey}
  deriving (Generic)

instance Eq Party where
  x == y = pid x == pid y && pkey x == pkey y

type Tx = ()

data Block = MkBlock
  { slotNumber :: SlotNumber
  , creatorId :: PartyId
  , parentBlock :: Hash Block
  , certificate :: Maybe Certificate
  , leadershipProof :: LeadershipProof
  , signature :: Signature
  , bodyHash :: Hash Payload
  }
  deriving (Generic)

data BlockBody = MkBlockBody
  { blockHash :: Hash Payload
  , payload :: Payload
  }
  deriving (Generic)

data Certificate = MkCertificate
  { round :: RoundNumber
  , blockRef :: Hash Block
  }
  deriving (Generic)

type Payload = [Tx]

instance Eq Certificate where
  x == y = round x == round y && blockRef x == blockRef y

instance Eq Block where
  x == y =
    slotNumber x == slotNumber y
      && creatorId x == creatorId y
      && parentBlock x == parentBlock y
      && leadershipProof x == leadershipProof y
      && certificate x == certificate y
      && signature x == signature y
      && bodyHash x == bodyHash y

instance Eq BlockBody where
  x == y = blockHash x == blockHash y && payload x == payload y

tipHash :: forall a. Hashable a => [a] -> Hash a
tipHash [] = MkHash emptyBS
tipHash (x : _) = hash x

instance Hashable Block where
  hash = MkHash . (\r -> bytesS r) . \r -> signature r
