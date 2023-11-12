module Peras.Crypto where
-- | Cryptographic primitives types and functions used to implement /Peras/ protocol.
--
-- We don't use real cryptography here, just a bunch of newtypes and
-- simple functions that represent various cryptographic operations
-- one can do when running the protocol

{-# FOREIGN AGDA2HS
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#-}

open import Level
open import Relation.Binary using (StrictTotalOrder)
open import Data.Unit
open import Data.Bool
postulate ByteString : Set
          emptyBS : ByteString
          _isInfixOf_ : ByteString → ByteString → Bool

record Hash : Set where
  field hash : ByteString
open Hash public
{-# COMPILE AGDA2HS Hash newtype deriving (Eq, Show) #-}
-- newtype stragegy not supported

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
  field proof : ByteString
open MembershipProof public
{-# COMPILE AGDA2HS MembershipProof newtype deriving (Eq, Show, Ord) #-}
-- newtype strategy not supported


record LeadershipProof : Set where
  field proof : ByteString
open LeadershipProof public
{-# COMPILE AGDA2HS LeadershipProof newtype deriving (Eq, Show) #-}
-- newtype strategy not supported

{-
-- use KES-based signatures which weighs about 600 bytes (could be
-- down to 400)
-}


record Signature : Set where
  field signature : ByteString
open Signature public
{-# COMPILE AGDA2HS Signature newtype deriving (Eq, Show, Ord) #-}
-- newtype strategy not supported

record VerificationKey : Set where
  field verKey : ByteString
open VerificationKey public
{-# COMPILE AGDA2HS VerificationKey newtype deriving (Eq, Show, Ord) #-}
-- newtype strategy not supported


-- | a fake membership "proof" is simply a concatenation of all the
-- members' verification keys.
isCommitteeMember : VerificationKey -> MembershipProof -> Bool
isCommitteeMember record {verKey = verKey} record {proof = proof} =
  verKey isInfixOf proof
{-# COMPILE AGDA2HS isCommitteeMember #-}

postulate verify : VerificationKey -> Signature -> ByteString -> Bool
