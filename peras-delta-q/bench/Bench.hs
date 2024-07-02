{-# LANGUAGE NumericUnderscores #-}

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Convolution (convolution, fftConvolution)
import Criterion (Benchmark, env, perRunEnv)
import Criterion.Main (bench, bgroup, defaultMain, nf, whnf)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Word (Word8)
import Test.QuickCheck (Gen, arbitrary, elements, generate, vectorOf)

main :: IO ()
main = do
  defaultMain
    [ benchConvolution
    , benchFFTConvolution
    ]

benchConvolution :: Benchmark
benchConvolution =
  bench "Direct convolution (100 elements)" $
    perRunEnv generateVectors $ \ ~(a, b) ->
      evaluate $ rnf $ convolution a b

benchFFTConvolution :: Benchmark
benchFFTConvolution =
  bench "FFT convolution (100 elements)" $
    perRunEnv generateVectors $ \ ~(a, b) ->
      evaluate $ rnf $ fftConvolution a b

generateVectors :: IO (Vector Double, Vector Double)
generateVectors = do
  a <- generate $ Vector.fromList <$> vectorOf 100 arbitrary
  b <- generate $ Vector.fromList <$> vectorOf 100 arbitrary
  pure (a, b)
