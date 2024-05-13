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

primHash :: H.Hashable a => a -> ByteString
primHash = LBS.toStrict . B.encode . H.hash
primHashUnit :: () -> ByteString
primHashUnit = primHash
primHashNat :: Natural -> ByteString
primHashNat = primHash
primHashBytes :: ByteString -> ByteString
primHashBytes = primHash

instance Hashable () where
  hash _ = MakeHash $ primHashUnit ()

instance Hashable ByteString where
  hash = MakeHash . primHashBytes

instance Hashable (Hash a) where
  hash = (MakeHash . primHashBytes) . \r -> hashBytes r

instance Hashable Natural where
  hash = MakeHash . primHashNat

instance Hashable a => Hashable ([a]) where
  hash =
    MakeHash
      . primHashBytes
      . concatBS
      . fmap (\x -> hashBytes (hash x))

instance (Hashable a, Hashable b) => Hashable ((a, b)) where
  hash (x, y) =
    MakeHash . primHashBytes $
      concatBS [hashBytes (hash x), hashBytes (hash y)]

instance
  (Hashable a, Hashable b, Hashable c) =>
  Hashable ((a, b, c))
  where
  hash (x, y, z) =
    MakeHash . primHashBytes $
      concatBS
        [hashBytes (hash x), hashBytes (hash y), hashBytes (hash z)]

castHash :: Hash a -> Hash b
castHash = MakeHash . \r -> hashBytes r

instance Hashable a => Hashable (Maybe a) where
  hash Nothing = castHash (hash ())
  hash (Just x) = castHash (hash ((), x))
