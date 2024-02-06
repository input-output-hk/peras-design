module Peras.RandomForks.Types (
  BlockId
, Currency
, PeerName(..)
, Slot
) where

import Data.UUID (UUID)

type BlockId = UUID

type Currency = Int

type Slot = Int

newtype PeerName = PeerName {getPeerName :: String}
  deriving (Eq, Ord, Read, Show)
