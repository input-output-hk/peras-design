-- | Cryptographic primitives types and functions used to implement /Peras/ protocol.
--
-- We don't use real cryptography here, just a bunch of newtypes and
-- simple functions that represent various cryptographic operations
-- one can do when running the protocol 
module Peras.Crypto where

open import Level
open import Relation.Binary using (StrictTotalOrder)
open import Data.Unit
open import Data.Bool

-- open import Haskell.Prelude

postulate
  ByteString : Set
  emptyBS : ByteString
  _isInfixOf_ : ByteString → ByteString → Bool

{-# FOREIGN AGDA2HS import Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}

record Hash : Set where
  field hash : ByteString

open Hash public

{-# COMPILE AGDA2HS Hash newtype #-}

postulate
  hsEq : Relation.Binary.Rel Hash 0ℓ
  hsLt : Relation.Binary.Rel Hash 0ℓ
  hsIs : Relation.Binary.IsStrictTotalOrder hsEq hsLt

HashO : StrictTotalOrder 0ℓ 0ℓ 0ℓ
HashO = record {
  Carrier            = Hash ;
  _≈_                = hsEq ;
  _<_                = hsLt ;
  isStrictTotalOrder = hsIs }

-- should use normal VRF algorithm like leadership membership
record MembershipProof : Set where
  field proofM : ByteString

open MembershipProof public

{-# COMPILE AGDA2HS MembershipProof newtype #-}

record LeadershipProof : Set where
  field proof : ByteString

open LeadershipProof public

{-# COMPILE AGDA2HS LeadershipProof newtype #-}


{-
-- use KES-based signatures which weighs about 600 bytes (could be
-- down to 400)
-}

record Signature : Set where
  field signature : ByteString

open Signature public

{-# COMPILE AGDA2HS Signature newtype #-}

record VerificationKey : Set where
  field verificationKey : ByteString

open VerificationKey public

{-# COMPILE AGDA2HS VerificationKey newtype #-}

-- | a fake membership "proof" is simply a concatenation of all the
-- members' verification keys.
isCommitteeMember : VerificationKey -> MembershipProof -> Bool
isCommitteeMember (record {verificationKey = verKey}) (record { proofM = proof }) =
  verKey isInfixOf proof

postulate verify : VerificationKey -> Signature -> ByteString -> Bool

