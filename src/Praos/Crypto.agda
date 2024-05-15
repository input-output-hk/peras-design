-- | Cryptographic primitives types and functions used to implement /Praos/ protocol.
--
-- We don't use real cryptography here, just a bunch of newtypes and
-- simple functions that represent various cryptographic operations
-- one can do when running the protocol
module Praos.Crypto where

open import Level
open import Relation.Binary using (StrictTotalOrder)
open import Data.Unit
open import Data.Bool
open import Relation.Binary using (DecidableEquality)

postulate
  ByteString : Set
  emptyBS : ByteString
  _isInfixOf_ : ByteString → ByteString → Bool

{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC emptyBS = BS.empty #-}
{-# COMPILE GHC _isInfixOf_ = BS.isInfixOf #-}

record Hash (a : Set) : Set where
  field hashBytes : ByteString

open Hash public

{-
postulate
  _≟-Hash_ : DecidableEquality Hash
-}

record Hashable (a : Set) : Set where
  field hash : a → Hash a

-- should use normal VRF algorithm like leadership membership
record MembershipProof : Set where
  field proofM : ByteString

open MembershipProof public

record LeadershipProof : Set where
  field proof : ByteString

open LeadershipProof public

{-
-- use KES-based signatures which weighs about 600 bytes (could be
-- down to 400)
-}

record Signature : Set where
  field bytes : ByteString

open Signature public

record VerificationKey : Set where
  field verificationKey : ByteString

open VerificationKey public

-- | a fake membership "proof" is simply a concatenation of all the
-- members' verification keys.
isCommitteeMember : VerificationKey -> MembershipProof -> Bool
isCommitteeMember (record {verificationKey = verKey}) (record { proofM = proof }) =
  verKey isInfixOf proof

postulate verify : VerificationKey -> Signature -> ByteString -> Bool
