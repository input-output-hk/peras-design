module Peras.Crypto where

import Data.ByteString as BS

newtype Hash = Hash {hash :: ByteString}
  deriving (Eq)

newtype MembershipProof = MembershipProof {proofM :: ByteString}
  deriving (Eq)

newtype LeadershipProof = LeadershipProof {proof :: ByteString}
  deriving (Eq)

newtype Signature = Signature {signature :: ByteString}
  deriving (Eq)

newtype VerificationKey = VerificationKey
  { verificationKey ::
      ByteString
  }
  deriving (Eq)
