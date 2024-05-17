{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Simulate.Types (
  Parameters (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Peras.Event (ByteSize)
import Peras.IOSim.Experiment (Experiment)
import Peras.IOSim.Network.Types (Delay)
import Peras.IOSim.Types (Coin)
import Peras.Numbering (SlotNumber)

data Parameters = Parameters
  { randomSeed :: Int
  , endSlot :: SlotNumber
  , peerCount :: Int
  , downstreamCount :: Int
  , totalStake :: Maybe Coin
  , maximumStake :: Coin
  , messageLatency :: Delay
  , messageBandwidth :: ByteSize
  , experiment :: Maybe Experiment
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Parameters
instance ToJSON Parameters
