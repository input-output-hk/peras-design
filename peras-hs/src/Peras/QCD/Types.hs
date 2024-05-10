{-# LANGUAGE DeriveGeneric #-}

module Peras.QCD.Types where

import Numeric.Natural (Natural)
import Peras.QCD.Crypto (ByteString, Hash (MakeHash), emptyBS)

import GHC.Generics (Generic)

newtype MembershipProof = MakeMembershipProof
  { membershipProofBytes ::
      ByteString
  }
  deriving (Generic, Show)

newtype LeadershipProof = MakeLeadershipProof
  { leadershipProofBytes ::
      ByteString
  }
  deriving (Generic, Show)

newtype Signature = MakeSignature {signatureBytes :: ByteString}
  deriving (Generic, Show)

newtype VerificationKey = MakeVerificationKey
  { verificationKeyBytes ::
      ByteString
  }
  deriving (Generic, Show)

type Slot = Natural

type Round = Natural

type PartyId = VerificationKey

type Weight = Natural

data Certificate = MakeCertificate
  { certificateRound :: Round
  , certificateBlock :: Hash Block
  , certificateBytes :: ByteString
  }
  deriving (Generic, Show)

type Tx = ()

data Block = MakeBlock
  { slot :: Slot
  , creator :: PartyId
  , parent :: Hash Block
  , certificate :: Maybe Certificate
  , leadershipProof :: LeadershipProof
  , signature :: Signature
  , bodyHash :: Hash [Tx]
  }
  deriving (Generic, Show)

data BlockBody = BlockBody
  { headerHash :: Hash Block
  , payload :: [Tx]
  }
  deriving (Generic, Show)

type Chain = [Block]

genesisHash :: Hash Block
genesisHash = MakeHash emptyBS

genesisCert :: Certificate
genesisCert = MakeCertificate 0 genesisHash emptyBS

certsOnChain :: Chain -> [Certificate]
certsOnChain [] = [genesisCert]
certsOnChain (block : chain) =
  maybe id (:) (certificate block) $ certsOnChain chain

lastCert :: Chain -> Certificate
lastCert [] = genesisCert
lastCert (block : chain) =
  maybe (lastCert chain) id (certificate block)

data Vote = MakeVote
  { voteRound :: Natural
  , voteParty :: PartyId
  , voteWeight :: Weight
  , voteBlock :: Hash Block
  , voteProof :: MembershipProof
  , voteSignature :: Signature
  }
  deriving (Generic, Show)

data Message
  = NewChain Chain
  | NewVote Vote
  deriving (Generic, Show)
