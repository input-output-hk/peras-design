{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Simulate.Types (
  Parameters (..),
) where

import GHC.Generics (Generic)
import Peras.Block (Slot)
import Peras.IOSim.Types (Currency)

import qualified Data.Aeson as A

data Parameters = Parameters
  { randomSeed :: Int
  , endSlot :: Slot
  , peerCount :: Int
  , downstreamCount :: Int
  , totalStake :: Maybe Currency
  , maximumStake :: Currency
  , messageDelay :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance A.FromJSON Parameters where
  parseJSON =
    A.withObject "Parameters" $
      \o ->
        do
          randomSeed <- o A..: "randomSeed"
          endSlot <- o A..: "endSlot"
          peerCount <- o A..: "peerCount"
          downstreamCount <- o A..: "downstreamCount"
          totalStake <- o A..: "totalStake"
          maximumStake <- o A..: "maximumStake"
          messageDelay <- o A..: "messageDelay"
          pure Parameters{..}

instance A.ToJSON Parameters where
  toJSON Parameters{..} =
    A.object
      [ "randomSeed" A..= randomSeed
      , "endSlot" A..= endSlot
      , "peerCount" A..= peerCount
      , "downstreamCount" A..= downstreamCount
      , "totalStake" A..= totalStake
      , "maximumStake" A..= maximumStake
      , "messageDelay" A..= messageDelay
      ]
