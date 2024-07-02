module Convolution where

import Data.Vector (Vector, (!))
import qualified Data.Vector as Vector
import FFT (irfft, rfft)

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
  m = length a + length b - 1
  result = Vector.replicate m 0
  -- pad each array with zeros
  a_padded = a <> Vector.replicate (m - length a) 0
  b_padded = b <> Vector.replicate (m - length b) 0

fftConvolution :: Vector Double -> Vector Double -> Vector Double
fftConvolution a b = irfft $ Vector.zipWith (*) (rfft a_padded) (rfft b_padded)
 where
  -- the length of the convolution
  m = length a + length b - 1
  -- pad each array with zeros
  a_padded = a <> Vector.replicate (m - length a) 0
  b_padded = b <> Vector.replicate (m - length b) 0
