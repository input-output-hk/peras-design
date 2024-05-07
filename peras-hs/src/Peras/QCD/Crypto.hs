{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Peras.QCD.Crypto where

import Numeric.Natural (Natural)

import qualified Data.Binary as B
import qualified Data.ByteString as BS (ByteString, concat, empty)
import qualified Data.ByteString.Lazy as LBS (toStrict)
import qualified Data.Hashable as H
import GHC.Generics (Generic)

type ByteString = BS.ByteString

type X = (Int, Int, Int)

emptyBS :: ByteString
emptyBS = BS.empty
concatBS :: [ByteString] -> ByteString
concatBS = BS.concat
eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)

newtype Hash a = MakeHash {hashBytes :: ByteString}
  deriving (Generic, Show)

instance Eq (Hash a) where
  x == y = eqBS (hashBytes x) (hashBytes y)

class Hashable a where
  hash :: a -> Hash a

unsafeHash :: H.Hashable a => a -> ByteString
unsafeHash = LBS.toStrict . B.encode . H.hash

instance Hashable ByteString where
  hash = MakeHash . unsafeHash

instance Hashable (Hash a) where
  hash = (MakeHash . unsafeHash) . \r -> hashBytes r

instance Hashable Natural where
  hash = MakeHash . unsafeHash

instance Hashable a => Hashable ([a]) where
  hash =
    MakeHash
      . unsafeHash
      . concatBS
      . fmap (\x -> hashBytes (hash x))

instance (Hashable a, Hashable b) => Hashable ((a, b)) where
  hash (x, y) =
    MakeHash $ unsafeHash (hashBytes (hash x), hashBytes (hash y))

instance
  (Hashable a, Hashable b, Hashable c) =>
  Hashable ((a, b, c))
  where
  hash (x, y, z) =
    MakeHash $
      unsafeHash
        (hashBytes (hash x), hashBytes (hash y), hashBytes (hash z))
