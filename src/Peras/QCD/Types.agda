module Peras.QCD.Types where

open import Data.Nat using (ℕ)
open import Haskell.Prelude
open import Peras.QCD.Crypto
open import Peras.QCD.Protocol

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
#-}

{-# FOREIGN GHC
import qualified Data.ByteString as BS
#-}

-- Cryptography types.

record MembershipProof : Set where
  constructor MakeMembershipProof
  field membershipProofBytes : ByteString
open MembershipProof public
{-# COMPILE AGDA2HS MembershipProof newtype deriving (Generic, Show) #-}

record LeadershipProof : Set where
  constructor MakeLeadershipProof
  field leadershipProofBytes : ByteString
open LeadershipProof public
{-# COMPILE AGDA2HS LeadershipProof newtype deriving (Generic, Show) #-}

record Signature : Set where
  constructor MakeSignature
  field signatureBytes : ByteString
open Signature public
{-# COMPILE AGDA2HS Signature newtype deriving (Generic, Show) #-}

record VerificationKey : Set where
  constructor MakeVerificationKey
  field verificationKeyBytes : ByteString
open VerificationKey public
{-# COMPILE AGDA2HS VerificationKey newtype deriving (Generic, Show) #-}

-- Basics.

Slot : Set
Slot = ℕ
{-# COMPILE AGDA2HS Slot #-}

Round : Set
Round = ℕ
{-# COMPILE AGDA2HS Round #-}

PartyId : Set
PartyId = VerificationKey
{-# COMPILE AGDA2HS PartyId #-}

-- Blocks.

record Certificate : Set

Tx : Set
Tx = ⊤
{-# COMPILE AGDA2HS Tx #-}

record Block : Set where
  constructor MakeBlock
  field slot : Slot
        creator : PartyId
        parent : Hash Block
        certificate : Maybe Certificate
        leadershipProof : LeadershipProof
        signature : Signature
        bodyHash : Hash (List Tx)
open Block public
{-# COMPILE AGDA2HS Block deriving (Generic, Show) #-}

record BlockBody : Set where
  field headerHash : Hash Block
        payload : List Tx
open BlockBody public
{-# COMPILE AGDA2HS BlockBody deriving (Generic, Show) #-}

-- Chains.

data Chain : Set where
  Genesis : Chain
  ChainBlock : Block → Chain → Chain
{-# COMPILE AGDA2HS Chain deriving (Generic, Show) #-}

genesisHash : Hash Block
genesisHash = record {hashBytes = emptyBS}
{-# COMPILE AGDA2HS genesisHash #-}

chainBlocks : Chain → List Block
chainBlocks Genesis = []
chainBlocks (ChainBlock block chain) = block ∷ chainBlocks chain
{-# COMPILE AGDA2HS chainBlocks #-}

-- Certificates.

record Certificate where
  constructor MakeCertificate
  field certificateRound : Round
        certificateBlock : Hash Block
        certificateBytes : ByteString
open Certificate public
{-# COMPILE AGDA2HS Certificate deriving (Generic, Show) #-}

genesisCert : Certificate
genesisCert = MakeCertificate 0 genesisHash emptyBS
{-# COMPILE AGDA2HS genesisCert #-}

certsOnChain : Chain → List Certificate
certsOnChain Genesis = genesisCert ∷ []
certsOnChain (ChainBlock block chain) = maybe id _∷_ (certificate block) $ certsOnChain chain
{-# COMPILE AGDA2HS certsOnChain #-}

lastCert : Chain → Certificate
lastCert Genesis = genesisCert
lastCert (ChainBlock block chain) = maybe (lastCert chain) id (certificate block)
{-# COMPILE AGDA2HS lastCert #-}

-- Votes.

record Vote : Set where
  constructor MakeVote
  field voteRound : ℕ
        voteParty : PartyId
        voteBlock : Hash Block
        voteProof : MembershipProof
        voteSignature : Signature
open Vote public
{-# COMPILE AGDA2HS Vote deriving (Generic, Show) #-}

-- Messages.

data Message : Set where
  NewChain : Chain → Message
  NewVote : Vote → Message
open Message public
{-# COMPILE AGDA2HS Message deriving (Generic, Show) #-}
