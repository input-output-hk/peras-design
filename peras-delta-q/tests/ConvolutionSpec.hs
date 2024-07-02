{-# LANGUAGE OverloadedLists #-}

module ConvolutionSpec where

import Control.Monad (forM_)
import Convolution (convolution, fftConvolution)
import Data.Vector ((!))
import Test.Hspec

spec :: Spec
spec = do
  it "computes the convolution of two lists" $ do
    convolution [1, 2, 3] [4, 5, 6] `shouldBe` [4, 13, 28, 27, 18]
    convolution [1 .. 5] [2, 4 .. 10] `shouldBe` [2, 8, 20, 40, 70, 88, 92, 80, 50]

  it "checks direct convolution is same as FFT convolution" $ do
    let a = [1, 2, 3, 4, 5]
    let b = [6, 7, 8, 9, 10]
    let c = convolution a b
    let d = fftConvolution a b
    forM_ ([0 .. (length c - 1)] :: [Int]) $
      \i -> (c ! i - d ! i) `shouldSatisfy` (< 1e-10)
