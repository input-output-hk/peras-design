{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Arbitraries where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Block (Block (..))
import Peras.Chain (Chain (..), RoundNumber (..), Vote (..))
import Peras.Crypto (
  Hash (..),
  LeadershipProof (..),
  MembershipProof (..),
  Signature (..),
  VerificationKey (..),
 )
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..), Gen, choose, vectorOf)
import Test.QuickCheck.Instances.Natural ()

instance Arbitrary Hash where
  arbitrary = Hash <$> genByteString 4

instance Arbitrary Signature where
  arbitrary = Signature <$> genByteString 4

instance Arbitrary LeadershipProof where
  arbitrary = LeadershipProof <$> genByteString 4

instance Arbitrary MembershipProof where
  arbitrary = MembershipProof <$> genByteString 4

instance Arbitrary VerificationKey where
  arbitrary = VerificationKey <$> genByteString 4

genByteString :: Int -> Gen ByteString
genByteString n = BS.pack <$> vectorOf n arbitrary

instance Arbitrary Block where
  arbitrary = genericArbitrary uniform
  shrink block@Block{payload} =
    [block{payload = payload'} | payload' <- shrink payload]

instance Arbitrary RoundNumber where
  arbitrary = RoundNumber <$> arbitrary

instance Arbitrary b => Arbitrary (Vote b) where
  arbitrary = MkVote <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary Chain where
  arbitrary = MkChain <$> arbitrary <*> arbitrary
