{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ConvolutionSpec where

import Convolution (convolution, fftConvolution, matrixConvolution)
import Data.Function ((&))
import Data.Vector.Storable (Vector, convert)
import qualified Data.Vector.Storable as Vector
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Arbitrary (..), Property, counterexample, (==>))

spec :: Spec
spec = do
  it "computes the convolution of two lists" $ do
    convolution [1, 2, 3] [4, 5, 6] `shouldBe` [4, 13, 28, 27, 18]
    convolution [1 .. 5] [2, 4 .. 10] `shouldBe` [2, 8, 20, 40, 70, 88, 92, 80, 50]

  prop "checks direct convolution is same as FFT convolution" prop_direct_vs_fft

  modifyMaxSuccess (const 200) $
    prop "checks direct convolution is same as hmatrix convolution" prop_direct_vs_hmatrix

instance Arbitrary (Vector Double) where
  arbitrary = Vector.fromList <$> arbitrary

prop_direct_vs_fft :: Vector Double -> Vector Double -> Property
prop_direct_vs_fft a b =
  let c = convolution a b
      d = fftConvolution (convert a) (convert b)
   in Vector.all (< 1e-9) (Vector.zipWith (-) c (convert d))
        & counterexample (show c <> " /= " <> show d)

prop_direct_vs_hmatrix :: Vector Double -> Vector Double -> Property
prop_direct_vs_hmatrix a b =
  not (Vector.null a)
    && not (Vector.null b)
    ==> let c = convolution a b
            d = matrixConvolution a b
         in Vector.all (< 1e-9) (Vector.zipWith (-) c d)
              & counterexample (show c <> " /= " <> show d)
