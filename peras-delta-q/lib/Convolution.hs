module Convolution where

import qualified Data.Vector as V
import Data.Vector.Generic (basicLength)
import Data.Vector.Storable (Vector, (!))
import qualified Data.Vector.Storable as Vector
import FFT (irfft, rfft)
import Numeric.LinearAlgebra (conv)

-- | Computes the convolution of two lists.
-- The convolution of two lists is defined as:

-- $$
-- (a * b)[n] = \sum_{k=0}^{M-1} a[k] b[n - k]

-- $$
--
-- see https://www.matecdev.com/posts/julia-fft-convolution.html
convolution :: Vector Double -> Vector Double -> Vector Double
convolution a b =
  Vector.imap
    ( \n _ ->
        Vector.sum $
          Vector.imap
            ( \k _ ->
                if (n - k) >= 0
                  then a_padded ! k * b_padded ! (n - k)
                  else 0
            )
            a_padded
    )
    result
 where
  -- the length of the convolution
  m = basicLength a + basicLength b - 1
  result = Vector.replicate m (0 :: Double)
  -- pad each array with zeros
  a_padded = a <> Vector.replicate (m - basicLength a) 0
  b_padded = b <> Vector.replicate (m - basicLength b) 0

-- | Computes the convolution of two lists using the FFT.
-- This function should be faster than `convolution` for large vectors but it's actually slower
-- because of the underlying library implementation based on native Haskell [matrix](https://hackage.haskell.org/package/matrix) package.
fftConvolution :: V.Vector Double -> V.Vector Double -> V.Vector Double
fftConvolution a b = irfft $ V.zipWith (*) (rfft a_padded) (rfft b_padded)
 where
  -- the length of the convolution
  m = length a + length b - 1
  -- pad each array with zeros
  a_padded = a <> V.replicate (m - length a) 0
  b_padded = b <> V.replicate (m - length b) 0

-- | Computes the convolution of two lists using the
-- [hmatrix](https://hackage.haskell.org/package/hmatrix-0.20.2/docs/Numeric-LinearAlgebra.html#v:conv)
-- package.
matrixConvolution :: Vector Double -> Vector Double -> Vector Double
matrixConvolution = conv
