module Peras.Crypto where

import Data.ByteString

newtype Hash = Hash {hashBytes :: ByteString}
  deriving (Eq)

class Hashable a where
  hash :: a -> Hash

newtype MembershipProof = MembershipProof {proofM :: ByteString}
  deriving (Eq)

newtype LeadershipProof = LeadershipProof {proof :: ByteString}
  deriving (Eq)

newtype Signature = Signature {bytes :: ByteString}
  deriving (Eq)

newtype VerificationKey = VerificationKey
  { verificationKey ::
      ByteString
  }
  deriving (Eq)
