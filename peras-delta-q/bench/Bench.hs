import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Monad (forM)
import Convolution (convolution, fftConvolution, matrixConvolution)
import Criterion (Benchmark, env, perRunEnv)
import Criterion.Main (bench, bgroup, defaultMain, nf, whnf)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Vector.Storable (Vector, convert)
import qualified Data.Vector.Storable as Vector
import Data.Word (Word8)
import Test.QuickCheck (Gen, arbitrary, elements, generate, vectorOf)

main :: IO ()
main = do
  defaultMain
    [ benchConvolution
    , benchMatrixConvolution [100, 1000, 10000]
    , benchFFTConvolution
    ]

benchConvolution :: Benchmark
benchConvolution =
  bench "Direct convolution (100 elements)" $
    perRunEnv (generateVectors 100) $ \ ~(a, b) ->
      evaluate $ rnf $ convolution a b

benchMatrixConvolution :: [Int] -> Benchmark
benchMatrixConvolution scale =
  bgroup
    "Matrix convolution"
    [benchMatrixConvolution' s | s <- scale]
 where
  benchMatrixConvolution' s =
    env (generateVectors s) $ \ ~(a, b) ->
      bench ("hmatrix convolution (" <> show s <> " elements)") $
        nf (uncurry matrixConvolution) (a, b)

benchFFTConvolution :: Benchmark
benchFFTConvolution =
  bench "FFT convolution (100 elements)" $
    perRunEnv (generateVectors 100) $ \ ~(a, b) ->
      evaluate $ rnf $ fftConvolution (convert a) (convert b)

generateVectors :: Int -> IO (Vector Double, Vector Double)
generateVectors size = do
  a <- generate $ Vector.fromList <$> vectorOf size arbitrary
  b <- generate $ Vector.fromList <$> vectorOf size arbitrary
  pure (a, b)
