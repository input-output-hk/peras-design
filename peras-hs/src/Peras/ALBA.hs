{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.ALBA where

import Control.Exception (bracket)
import Control.Monad (forM)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.ByteString.Internal (toForeignPtr0)
import Data.Functor (void)
import Data.Maybe (catMaybes)
import Data.Ratio ((%))
import Data.Serialize (encode)
import Debug.Trace (trace)
import Foreign (Ptr, Word8, free, mallocBytes, peekArray, withForeignPtr)
import System.IO.Unsafe (unsafePerformIO)
import System.Random.Stateful (Uniform (uniformM))

foreign import capi unsafe "blake2b.h blake2b256_hash" blake2b256_hash :: Ptr Word8 -> Int -> Ptr Word8 -> IO Int

-- | ALBA parameters.
--
-- The goal of ALBA is that given a set of elements $S_p$ known to the prover,
-- such that $|S_p| \geq n_p$, the prover can convince the verifier that $|S_p| \geq n_f$
-- with $n_f < n_p$.
data Params = Params
  { λ_sec :: Integer
  -- ^ Security parameter
  -- Controls the probability that `extract` returns a set of size less than `n_f`.
  -- 128 seems like a good value
  , λ_rel :: Integer
  -- ^ Verification parameter.
  -- Controls the probability that `verify` returns `True` when the proof is invalid.
  -- 128 seems like a good value
  , n_p :: Integer
  -- ^ Size of "honest" parties
  , n_f :: Integer
  -- ^ Size of "adversarial" parties.
  }
  deriving (Show)

-- | A "random oracle" producing some bytestring of given length for a given input.
type H a = a -> Int -> ByteString

-- | Weight function for type `a`.
type W a = a -> Int

newtype Proof = Proof (Integer, [ByteString])
  deriving (Show)

class Hashable a where
  hash :: a -> ByteString

instance Hashable Integer where
  hash = hash . encode

instance Hashable ByteString where
  hash bytes =
    unsafePerformIO $ bracket (mallocBytes 32) free $ \out ->
      let (foreignPtr, len) = toForeignPtr0 bytes
       in withForeignPtr foreignPtr $ \ptr -> do
            void $ blake2b256_hash ptr len out
            BS.pack <$> peekArray 32 out

instance Hashable a => Hashable [a] where
  hash = hash . BS.concat . map hash

instance (Hashable a, Hashable b) => Hashable (a, b) where
  hash (a, b) = hash $ hash a <> hash b

-- | Output a proof `the set of elements known to the prover `s_p` has size greater than $n_f$.
prove :: Params -> [ByteString] -> Proof
prove params@Params{n_p} s_p =
  go (fromInteger u - 1) round0
 where
  round0 = [(t, [s_i]) | s_i <- s_p, t <- [1 .. d]]

  (u, d, q) = computeParams params

  h1 :: Hashable a => a -> Integer -> Bool
  h1 a n =
    let !h = hash a
        !m = h `modBS` n
     in m == 0

  go :: Int -> [(Integer, [ByteString])] -> Proof
  go 0 acc =
    let prob = ceiling $ 1 / q
        s_p'' = filter (flip h1 prob) acc
     in Proof $ head s_p''
  go n acc =
    let s_p' = filter (flip h1 n_p) acc
        s_p'' = [(t, s_i : s_j) | s_i <- s_p, (t, s_j) <- s_p']
     in go (n - 1) s_p''

computeParams :: Params -> (Integer, Integer, Double)
computeParams Params{λ_rel, λ_sec, n_p, n_f} =
  (u, d, q)
 where
  e = exp 1

  loge :: Double
  loge = logBase 2 e

  u =
    ceiling $
      (fromIntegral λ_sec + logBase 2 (fromIntegral λ_rel) + 1 + logBase 2 loge)
        / logBase 2 (fromIntegral n_p / fromIntegral n_f)

  d = (2 * u * λ_rel) `div` floor loge

  q :: Double
  q = 2 * fromIntegral λ_rel / (fromIntegral d * loge)

modBS :: ByteString -> Integer -> Integer
modBS bs q =
  let n = BS.foldl' (\acc b -> (acc * 256 + fromIntegral b) `mod` q) 0 bs
   in n `mod` q

-- | Verify `Proof` that the set of elements known to the prover `s_p` has size greater than $n_f$.
verify :: Params -> Proof -> Bool
verify params@Params{n_p} (Proof (d, bs)) =
  let (u, _, q) = computeParams params

      fo item (0, n, acc) =
        let prf = item : acc
            toh = (n, prf)
            prob = ceiling $ 1 / q
            h = hash toh
            m =
              if length prf < length bs
                then modBS h n_p
                else modBS h prob
         in (m, n, item : acc)
      fo _ (k, n, acc) = (k, n, acc)

      fst3 (a, _, _) = a
   in length bs == fromInteger u
        && ((== 0) . fst3) (foldr fo (0, d, []) bs)
