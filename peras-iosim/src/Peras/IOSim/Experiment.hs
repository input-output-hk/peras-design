{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}

module Peras.IOSim.Experiment (
  Experiment (..),
  Veto,
  experimentFactory,
  noVeto,
  splitBrain,
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Function (on)
import Data.Hashable (Hashable (hash))
import GHC.Generics (Generic)
import Peras.IOSim.Message.Types (OutEnvelope (..))
import Peras.Message (NodeId (MkNodeId))
import Peras.Numbering (SlotNumber (..))

data Experiment
  = NoExperiment
  | SplitBrain
      { experimentStart :: SlotNumber
      , experimentFinish :: SlotNumber
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Experiment
instance ToJSON Experiment

type Veto = OutEnvelope -> SlotNumber -> Bool

noVeto :: Veto
noVeto = const $ const False

experimentFactory :: Experiment -> Veto
experimentFactory NoExperiment = noVeto
experimentFactory SplitBrain{..} = splitBrain experimentStart experimentFinish

splitBrain :: SlotNumber -> SlotNumber -> Veto
splitBrain _ _ Idle _ = False
splitBrain (MkSlotNumber start) (MkSlotNumber finish) OutEnvelope{..} (MkSlotNumber now) =
  let
    parity :: NodeId -> Bool
    parity (MkNodeId s) = (== 0) . (`mod` 2) $ hash s
   in
    start <= now
      && now <= finish
      && on (/=) parity source destination
