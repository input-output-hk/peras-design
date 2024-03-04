{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Protocol.Types (
  Protocol (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Data.Default (Default(..))

data Protocol = Peras
  { activeSlotCoefficient :: Double
  , pCommitteeLottery :: Double
  , roundDuration :: Natural
  , votingBoost :: Double
  , votingWindow :: (Natural, Natural)
  , votingQuorum :: Int
  , voteMaximumAge :: Natural
  , cooldownDuration :: Natural
  , prefixCutoffWeight :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance Default Protocol where
  def =
    Peras
    {
      activeSlotCoefficient = 0.05
    , roundDuration = 10
    , pCommitteeLottery = 0.00021
    , votingBoost = 0.25
    , votingWindow = (50, 1)
    , votingQuorum = 10
    , voteMaximumAge = 30
    , cooldownDuration = 5
    , prefixCutoffWeight =  10000000
    }

instance FromJSON Protocol
instance ToJSON Protocol
