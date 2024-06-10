{-# LANGUAGE DeriveGeneric #-}

module Peras.Crypto where

import Data.ByteString (ByteString)

import GHC.Generics (Generic)

eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)

newtype Hash a = MkHash {hashBytes :: ByteString}
  deriving (Generic)

instance Eq (Hash a) where
  x == y = eqBS (hashBytes x) (hashBytes y)

class Hashable a where
  hash :: a -> Hash a

newtype MembershipProof = MkMembershipProof {proofM :: ByteString}
  deriving (Generic)

instance Eq MembershipProof where
  x == y = eqBS (proofM x) (proofM y)

newtype LeadershipProof = MkLeadershipProof {proofL :: ByteString}
  deriving (Generic)

instance Eq LeadershipProof where
  x == y = eqBS (proofL x) (proofL y)

newtype Signature = MkSignature {bytesS :: ByteString}
  deriving (Generic)

instance Eq Signature where
  x == y = eqBS (bytesS x) (bytesS y)

newtype VerificationKey = MkVerificationKey {keyV :: ByteString}
  deriving (Generic)

instance Eq VerificationKey where
  x == y = eqBS (keyV x) (keyV y)
