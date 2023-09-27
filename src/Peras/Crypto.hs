{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Cryptographic primitives types and functions used to implement /Peras/ protocol.
--
-- We don't use real cryptography here, just a bunch of newtypes and
-- simple functions that represent various cryptographic operations
-- one can do when running the protocol
module Peras.Crypto where

import Data.ByteString (ByteString, isInfixOf)

newtype Hash = Hash {hash :: ByteString}
  deriving newtype (Eq, Show)

-- should use normal VRF algorithm like leadership membership
newtype MembershipProof = MembershipProof {proof :: ByteString}
  deriving newtype (Eq, Show, Ord)

newtype LeadershipProof = LeadershipProof {proof :: ByteString}
  deriving newtype (Eq, Show)

-- use KES-based signatures which weighs about 600 bytes (could be
-- down to 400)
newtype Signature = Signature {signature :: ByteString}
  deriving newtype (Eq, Show, Ord)

newtype VerificationKey = VerificationKey {verKey :: ByteString}
  deriving newtype (Eq, Show, Ord)

-- | a fake membership "proof" is simply a concatenation of all the
-- members' verification keys.
isCommitteeMember :: VerificationKey -> MembershipProof -> Bool
isCommitteeMember VerificationKey{verKey} MembershipProof{proof} =
  verKey `isInfixOf` proof

verify :: VerificationKey -> Signature -> ByteString -> Bool
verify vkey sign bytes = undefined
