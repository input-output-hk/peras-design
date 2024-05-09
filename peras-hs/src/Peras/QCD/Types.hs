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

data Chain
  = Genesis
  | ChainBlock Block Chain
  deriving (Generic, Show)

genesisHash :: Hash Block
genesisHash = MakeHash emptyBS

chainBlocks :: Chain -> [Block]
chainBlocks Genesis = []
chainBlocks (ChainBlock block chain) = block : chainBlocks chain

genesisCert :: Certificate
genesisCert = MakeCertificate 0 genesisHash emptyBS

certsOnChain :: Chain -> [Certificate]
certsOnChain Genesis = [genesisCert]
certsOnChain (ChainBlock block chain) =
  maybe id (:) (certificate block) $ certsOnChain chain

lastCert :: Chain -> Certificate
lastCert Genesis = genesisCert
lastCert (ChainBlock block chain) =
  maybe (lastCert chain) id (certificate block)

data Vote = Vote
  { voteRound :: Natural
  , voteParty :: PartyId
  , voteBlock :: Hash Block
  , voteProof :: MembershipProof
  , voteSignature :: Signature
  }
  deriving (Generic, Show)

data Message
  = NewChain Chain
  | NewVote Vote
  deriving (Generic, Show)
