{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Simulate.Types (
  Parameters (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.IOSim.Types (Coin)

data Parameters = Parameters
  { randomSeed :: Int
  , endSlot :: Slot
  , peerCount :: Int
  , downstreamCount :: Int
  , totalStake :: Maybe Coin
  , maximumStake :: Coin
  , messageDelay :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Parameters
instance ToJSON Parameters
