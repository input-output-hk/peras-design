-- | Cryptographic primitives types and functions used to implement /Peras/ protocol.
--
-- We don't use real cryptography here, just a bunch of newtypes and
-- simple functions that represent various cryptographic operations
-- one can do when running the protocol
module Peras.Crypto where

open import Data.Bool using (Bool)
open import Haskell.Prelude using (Eq; _==_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary using (StrictTotalOrder)

-- The following implementations are supplied in Haskell.
postulate
  ByteString : Set
  emptyBS : ByteString
  eqBS : ByteString → ByteString → Bool
  _isInfixOf_ : ByteString → ByteString → Bool
  _≟_ : DecidableEquality ByteString

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics (Generic)
eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)
#-}

{-# FOREIGN GHC
import qualified Data.ByteString as BS
import qualified Peras.Crypto as G
#-}

{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC emptyBS = BS.empty #-}
{-# COMPILE GHC eqBS = (==) #-}
{-# COMPILE GHC _isInfixOf_ = BS.isInfixOf #-}

record Hash (a : Set) : Set where
  constructor MkHash
  field hashBytes : ByteString

open Hash public

{-# COMPILE AGDA2HS Hash newtype deriving (Generic) #-}
{-# COMPILE GHC Hash = data G.Hash (G.MkHash) #-}

instance
  iHashEq : {a : Set} → Eq (Hash a)
  iHashEq ._==_ x y = eqBS (hashBytes x) (hashBytes y)

{-# COMPILE AGDA2HS iHashEq #-}

record Hashable (a : Set) : Set where
  field hash : a → Hash a

{-# COMPILE AGDA2HS Hashable class #-}

-- should use normal VRF algorithm like leadership membership
record MembershipProof : Set where
  constructor MkMembershipProof
  field proofM : ByteString

open MembershipProof public

{-# COMPILE AGDA2HS MembershipProof newtype deriving (Generic) #-}
{-# COMPILE GHC MembershipProof = data G.MembershipProof (G.MkMembershipProof) #-}

instance
  iMembershipProofEq : Eq MembershipProof
  iMembershipProofEq ._==_ x y = eqBS (proofM x) (proofM y)

{-# COMPILE AGDA2HS iMembershipProofEq #-}

record LeadershipProof : Set where
  constructor MkLeadershipProof
  field proofL : ByteString

open LeadershipProof public

{-# COMPILE AGDA2HS LeadershipProof newtype deriving (Generic) #-}
{-# COMPILE GHC LeadershipProof = data G.LeadershipProof (G.MkLeadershipProof) #-}

instance
  iLeadershipProofEq : Eq LeadershipProof
  iLeadershipProofEq ._==_ x y = eqBS (proofL x) (proofL y)

{-# COMPILE AGDA2HS iLeadershipProofEq #-}

{-
-- use KES-based signatures which weighs about 600 bytes (could be
-- down to 400)
-}

record Signature : Set where
  constructor MkSignature
  field bytesS : ByteString

open Signature public

{-# COMPILE AGDA2HS Signature newtype deriving (Generic) #-}
{-# COMPILE GHC Signature = data G.Signature (G.MkSignature) #-}

instance
  iSignatureEq : Eq Signature
  iSignatureEq ._==_ x y = eqBS (bytesS x) (bytesS y)

{-# COMPILE AGDA2HS iSignatureEq #-}

record VerificationKey : Set where
  constructor MkVerificationKey
  field keyV : ByteString

open VerificationKey public

{-# COMPILE AGDA2HS VerificationKey newtype deriving (Generic) #-}
{-# COMPILE GHC VerificationKey = data G.VerificationKey (G.MkVerificationKey) #-}

instance
  iVerificationKeyEq : Eq VerificationKey
  iVerificationKeyEq ._==_ x y = eqBS (keyV x) (keyV y)

{-# COMPILE AGDA2HS iVerificationKeyEq #-}

-- | a fake membership "proof" is simply a concatenation of all the
-- members' verification keys.
isCommitteeMember : VerificationKey -> MembershipProof -> Bool
isCommitteeMember (record {keyV = verKey}) (record { proofM = proof }) =
  verKey isInfixOf proof

postulate verify : VerificationKey -> Signature -> ByteString -> Bool
