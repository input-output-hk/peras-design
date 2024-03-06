{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Arbitraries where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Generic.Random (genericArbitrary, uniform)
import Numeric.Natural (Natural)
import Peras.Block (Block (..))
import Peras.Chain (Chain (..), RoundNumber (..), Vote (..))
import Peras.Crypto (
  Hash (..),
  LeadershipProof (..),
  MembershipProof (..),
  Signature (..),
  VerificationKey (..),
 )
import Peras.Event (Event, UniqueId (..))
import Peras.Message (Message, NodeId (..))
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..), Gen, vectorOf)
import Test.QuickCheck.Instances.Natural ()
import Test.QuickCheck.Instances.Time ()

instance Arbitrary NodeId where
  arbitrary =
    MkNodeId
      <$> (("Node-" <>) . show <$> (arbitrary @Natural))

instance Arbitrary Hash where
  arbitrary = Hash <$> genByteString 8

instance Arbitrary Signature where
  arbitrary = Signature <$> genByteString 8

instance Arbitrary LeadershipProof where
  arbitrary = LeadershipProof <$> genByteString 8

instance Arbitrary MembershipProof where
  arbitrary = MembershipProof <$> genByteString 8

instance Arbitrary VerificationKey where
  arbitrary = VerificationKey <$> genByteString 8

genByteString :: Int -> Gen ByteString
genByteString n = BS.pack <$> vectorOf n arbitrary

instance Arbitrary Block where
  arbitrary = genericArbitrary uniform
  shrink block@Block{payload} =
    [block{payload = payload'} | payload' <- shrink payload]

instance Arbitrary RoundNumber where
  arbitrary = MkRoundNumber <$> arbitrary

instance Arbitrary Vote where
  arbitrary =
    MkVote
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary Chain where
  arbitrary = MkChain <$> arbitrary <*> arbitrary

instance Arbitrary Message where
  arbitrary = genericArbitrary uniform

instance Arbitrary UniqueId where
  arbitrary = UniqueId <$> genByteString 8

instance Arbitrary Event where
  arbitrary = genericArbitrary uniform
