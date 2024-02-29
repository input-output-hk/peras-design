{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Protocol.Types (
  Protocol (..),
) where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)

data Protocol
  = -- | Low-fidelity version of OuroborosPraos.
    PseudoPraos
      { activeSlotCoefficient :: Double
      }
  | -- | Low-fidelity version of Ouroboros Peras.
    PseudoPeras
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
  | -- | High-fidelity version of Ouroboros Praos.
    OuroborosPraos
  | -- | High-fidelity version of Ouroboros Genesis.
    OuroborosGenesis
  | -- | High-fidelity version of Ouroboros Peras.
    OuroborosPeras
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Protocol
instance ToJSON Protocol
