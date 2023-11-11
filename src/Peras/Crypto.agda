{-

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Cryptographic primitives types and functions used to implement /Peras/ protocol.
--
-- We don't use real cryptography here, just a bunch of newtypes and
-- simple functions that represent various cryptographic operations
-- one can do when running the protocol

-}
module Peras.Crypto where

open import Level
open import Relation.Binary using (StrictTotalOrder)
open import Data.Unit
open import Data.Bool

postulate ByteString : Set
          emptyBS : ByteString
          _isInfixOf_ : ByteString → ByteString → Bool

record Hash : Set where
  field hash : ByteString
--  deriving newtype (Eq, Show)

postulate hsEq : Relation.Binary.Rel Hash zero
postulate hsLt : Relation.Binary.Rel Hash zero
postulate hsIs : Relation.Binary.IsStrictTotalOrder hsEq hsLt

HashO : StrictTotalOrder zero zero zero
HashO = record {
  Carrier            = Hash ;
  _≈_                = hsEq ;
  _<_                = hsLt ;
  isStrictTotalOrder = hsIs }


-- should use normal VRF algorithm like leadership membership
record MembershipProof : Set where
  constructor membershipProof
  field proof : ByteString
--   deriving newtype (Eq, Show, Ord)



record LeadershipProof : Set where
  field proof : ByteString
--  deriving newtype (Eq, Show)

{-
-- use KES-based signatures which weighs about 600 bytes (could be
-- down to 400)
-}


record Signature : Set where
  field signature : ByteString
--  deriving newtype (Eq, Show, Ord)


record VerificationKey : Set where
  constructor verificationKey
  field verKey : ByteString
  -- deriving newtype (Eq, Show, Ord)


-- | a fake membership "proof" is simply a concatenation of all the
-- members' verification keys.
isCommitteeMember : VerificationKey -> MembershipProof -> Bool
isCommitteeMember (verificationKey verKey) (membershipProof proof) =
  verKey isInfixOf proof

postulate verify : VerificationKey -> Signature -> ByteString -> Bool

