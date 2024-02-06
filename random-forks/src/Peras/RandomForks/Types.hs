module Peras.RandomForks.Types (
  BlockId
, Currency
, PeerName(..)
, Slot
) where

import Data.ByteString.Short  (ShortByteString)

type BlockId = ShortByteString

type Currency = Int

type Slot = Int

newtype PeerName = PeerName {getPeerName :: String}
  deriving (Eq, Ord, Read, Show)
