{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Peras.Arbitraries where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Peras.Block (Block (..), PartyId (..), Tx (..))
import Peras.Chain (Chain (..), asChain)
import Peras.Crypto (Hash (..), LeadershipProof (..), Signature (..), VerificationKey (..))
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (..), Gen, choose, vectorOf)
import Test.QuickCheck.Instances.Natural ()

instance Arbitrary Tx where
  arbitrary = Tx <$> (choose (50, 500) >>= genByteString)

instance Arbitrary Hash where
  arbitrary = Hash <$> genByteString 4

instance Arbitrary Signature where
  arbitrary = Signature <$> genByteString 4

instance Arbitrary LeadershipProof where
  arbitrary = LeadershipProof <$> genByteString 4

instance Arbitrary VerificationKey where
  arbitrary = VerificationKey <$> genByteString 4

genByteString :: Int -> Gen ByteString
genByteString n = BS.pack <$> vectorOf n arbitrary

instance Arbitrary PartyId where
  arbitrary = MkPartyId <$> arbitrary

instance (Arbitrary t, Generic t) => Arbitrary (Block t) where
  arbitrary = genericArbitrary uniform
  shrink block@Block{payload} =
    [block{payload = payload'} | payload' <- shrink payload]

instance (Arbitrary t, Generic t) => Arbitrary (Chain t) where
  arbitrary = asChain <$> arbitrary

  shrink = \case
    Genesis -> []
    Cons _ cs -> [cs]
