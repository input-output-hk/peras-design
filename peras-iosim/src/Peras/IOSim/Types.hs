{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Types (
  ByteSize,
  Coin,
  Rollback (..),
  Vote',
  Message',
) where

import Data.Aeson (FromJSON, ToJSON)
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

type Message' = Message Block

type Vote' = Vote Hash

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
