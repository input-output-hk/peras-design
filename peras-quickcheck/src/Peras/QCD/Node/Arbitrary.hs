{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.QCD.Node.Arbitrary where

import Peras.QCD.Crypto
import Peras.QCD.Protocol (Params, defaultParams)
import Peras.QCD.Types
import Peras.QCD.Types.Instances ()
import Test.QuickCheck (Arbitrary (..), Gen, vectorOf)
import Test.QuickCheck.Instances.Natural ()

import qualified Data.ByteString as BS

instance Arbitrary Params where
  -- FIXME: Generate a reasonable set of arbitrary parameters.
  arbitrary = pure defaultParams

instance Arbitrary ByteString where
  arbitrary = genByteString 8

instance Arbitrary VerificationKey where
  arbitrary = MakeVerificationKey <$> arbitrary

genByteString :: Int -> Gen ByteString
genByteString n = BS.pack <$> vectorOf n arbitrary
