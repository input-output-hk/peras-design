{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Arbitraries where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Generic.Random (genericArbitrary, uniform)
import Numeric.Natural (Natural)
import Peras.Block (Block (..), BlockBody (..), Certificate (..))
import Peras.Chain (Vote (..))
import Peras.Crypto (
  Hash (..),
  LeadershipProof (..),
  MembershipProof (..),
  Signature (..),
  VerificationKey (..),
 )
import Peras.Event (Event, Rollback, UniqueId (..))
import Peras.Message (Message, NodeId (..))
import Peras.Numbering (RoundNumber (..), SlotNumber (..))
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..), Gen, vectorOf)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Instances.Natural ()
import Test.QuickCheck.Instances.Time ()
import Test.QuickCheck.Random (mkQCGen)

-- | Utility function for pure arbitrary values.
generateWith :: Gen a -> Int -> a
generateWith (MkGen runGen) seed =
  runGen (mkQCGen seed) 30

instance Arbitrary NodeId where
  arbitrary =
    MkNodeId
      <$> (("Node-" <>) . show <$> (arbitrary @Natural))

instance Arbitrary a => Arbitrary (Hash a) where
  arbitrary = MkHash <$> genByteString 8

instance Arbitrary Signature where
  arbitrary = MkSignature <$> genByteString 8

instance Arbitrary LeadershipProof where
  arbitrary = MkLeadershipProof <$> genByteString 8

instance Arbitrary MembershipProof where
  arbitrary = MkMembershipProof <$> genByteString 8

instance Arbitrary VerificationKey where
  arbitrary = MkVerificationKey <$> genByteString 8

genByteString :: Int -> Gen ByteString
genByteString n = BS.pack <$> vectorOf n arbitrary

instance Arbitrary Certificate where
  arbitrary = genericArbitrary uniform

instance Arbitrary Block where
  arbitrary = genericArbitrary uniform

instance Arbitrary BlockBody where
  arbitrary = genericArbitrary uniform
  shrink block@MkBlockBody{payload} =
    [block{payload = payload'} | payload' <- shrink payload]

instance Arbitrary RoundNumber where
  arbitrary = MkRoundNumber <$> arbitrary

instance Arbitrary SlotNumber where
  arbitrary = MkSlotNumber <$> arbitrary

instance Arbitrary Vote where
  arbitrary =
    MkVote
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary Message where
  arbitrary = genericArbitrary uniform

instance Arbitrary UniqueId where
  arbitrary = UniqueId <$> genByteString 8

instance Arbitrary Event where
  arbitrary = genericArbitrary uniform

instance Arbitrary Rollback where
  arbitrary = genericArbitrary uniform
