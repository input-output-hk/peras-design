{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Types (
  ByteSize,
  Coin,
  Rollback (..),
  Votes,
  Vote',
  Blocks,
  Message',
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Map (Map)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Vote)
import Peras.Crypto (Hash)
import Peras.Message (Message)
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Instances.Natural ()

type Coin = Int

type ByteSize = Word

type Blocks = Map Hash Block

type Message' = Message Block

type Vote' = Vote Hash

type Votes = Map Hash Vote'

data Rollback = Rollback
  { atSlot :: Slot
  , slots :: Natural
  , blocks :: Natural
  , fromWeight :: Double
  , toWeight :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Rollback
instance ToJSON Rollback

instance Arbitrary Rollback where
  arbitrary = genericArbitrary uniform
