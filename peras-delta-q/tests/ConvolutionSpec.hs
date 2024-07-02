{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ConvolutionSpec where

import Convolution (convolution, fftConvolution)
import Data.Function ((&))
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (..), Property, counterexample)

spec :: Spec
spec = do
  it "computes the convolution of two lists" $ do
    convolution [1, 2, 3] [4, 5, 6] `shouldBe` [4, 13, 28, 27, 18]
    convolution [1 .. 5] [2, 4 .. 10] `shouldBe` [2, 8, 20, 40, 70, 88, 92, 80, 50]

  prop "checks direct convolution is same as FFT convolution" $ prop_direct_vs_fft

instance Arbitrary (Vector Double) where
  arbitrary = Vector.fromList <$> arbitrary

prop_direct_vs_fft :: Vector Double -> Vector Double -> Property
prop_direct_vs_fft a b =
  let c = convolution a b
      d = fftConvolution a b
   in all (< 1e-9) (Vector.zipWith (-) c d)
        & counterexample (show c <> " /= " <> show d)
