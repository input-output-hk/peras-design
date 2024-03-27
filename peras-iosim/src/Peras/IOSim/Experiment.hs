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
import Peras.Block (Slot)
import Peras.IOSim.Message.Types (OutEnvelope (..))
import Peras.Message (NodeId (MkNodeId))

data Experiment
  = NoExperiment
  | SplitBrain
      { experimentStart :: Slot
      , experimentFinish :: Slot
      }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Experiment
instance ToJSON Experiment

type Veto = OutEnvelope -> Slot -> Bool

noVeto :: Veto
noVeto = const $ const False

experimentFactory :: Experiment -> Veto
experimentFactory NoExperiment = noVeto
experimentFactory SplitBrain{..} = splitBrain experimentStart experimentFinish

splitBrain :: Slot -> Slot -> Veto
splitBrain _ _ Idle _ = False
splitBrain start finish OutEnvelope{..} now =
  let
    parity :: NodeId -> Bool
    parity (MkNodeId s) = (== 0) . (`mod` 2) $ hash s
   in
    start <= now
      && now <= finish
      && on (/=) parity source destination
