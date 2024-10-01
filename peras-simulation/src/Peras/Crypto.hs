{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Peras.Crypto where

import Data.ByteString (ByteString)

import Data.ByteString as BS
import Data.Word (Word8)
import GHC.Generics (Generic)

eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)
replicateBS :: Int -> Word8 -> ByteString
replicateBS = BS.replicate
emptyBS :: ByteString
emptyBS = mempty

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
