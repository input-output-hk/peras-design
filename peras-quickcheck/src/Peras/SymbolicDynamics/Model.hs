{-# LANGUAGE DeriveGeneric #-}

module Peras.SymbolicDynamics.Model (
  Currency,
  Operation,
  VoteWeight,
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Map (Map)
import Data.Set (Set)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Certificate, PartyId, Slot)
import Peras.Chain (RoundNumber, Vote)
import Peras.Crypto (Hash)
import Peras.Message (NodeId)
import Peras.Orphans ()

type Currency = Natural

type VoteWeight = Natural

data Operation
  = DeclareNode
      { node :: NodeId
      , party :: PartyId
      }
  | SetStake
      { node :: NodeId
      , stake :: Currency
      }
  | SetHonesty
      { node :: NodeId
      , honesty :: Honesty
      }
  | BeginSlot
      { slot :: Slot
      , leaders :: Set NodeId
      }
  | BeginRound
      { roundNumber :: RoundNumber
      , voters :: Map NodeId VoteWeight
      }
  | ForgeBlock
      { node :: NodeId
      , block :: Block
      }
  | CastVote
      { node :: NodeId
      , vote :: Vote
      }
  | BuildCertificate
      { node :: NodeId
      , certificate :: Certificate
      }
  | VerifyBlock
      { node :: NodeId
      , blockHash :: Hash Block
      }
  | VerifyVote
      { node :: NodeId
      , voteHash :: Hash Vote
      }
  | VerifyCertificate
      { node :: NodeId
      , certificateHash :: Hash Certificate
      }
  | AdoptChain
      { node :: NodeId
      , tip :: Hash Block
      }
  | DiffuseBlock
      { node :: NodeId
      , destinations :: Destinations
      , blockHash :: Hash Block
      }
  | DiffuseVote
      { node :: NodeId
      , destinations :: Destinations
      , voteHash :: Hash Vote
      }
  | DiffuseCertificate
      { node :: NodeId
      , destinations :: Destinations
      , certificateHash :: Hash Certificate
      }
  deriving (Eq, Generic, Ord, Read, Show)

instance FromJSON Operation
instance ToJSON Operation

data Honesty
  = Honest
  | Adversarial (Set Dishonesty)
  deriving (Eq, Generic, Ord, Read, Show)

instance FromJSON Honesty
instance ToJSON Honesty

data Dishonesty
  = NeverCastVote
  | NeverForgeCertificate
  | EquivocateBlock
  | EquivocateVote
  | EquivocateCertificate
  deriving (Eq, Generic, Ord, Read, Show)

instance FromJSON Dishonesty
instance ToJSON Dishonesty

data Destinations
  = AllNodes
  | SomeNodes (Set NodeId)
  deriving (Eq, Generic, Ord, Read, Show)

instance FromJSON Destinations
instance ToJSON Destinations
