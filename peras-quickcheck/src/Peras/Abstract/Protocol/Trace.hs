{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Peras.Abstract.Protocol.Trace where

import Control.Tracer (Tracer (..), contramap, stdoutTracer)
import Data.Aeson (FromJSON, ToJSON)
import qualified Data.Aeson as A
import Data.Set (Set)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LE
import GHC.Generics (Generic)
import Peras.Chain (Chain, Vote)
import Peras.Numbering (SlotNumber)
import Peras.Orphans ()

data PerasLog
  = Tick SlotNumber
  | NewChainAndVotes {newChains :: Set Chain, newVotes :: Set Vote}
  | NewChainPref {newChainPref :: Chain}
  deriving stock (Show, Eq, Generic)
  deriving anyclass (ToJSON, FromJSON)

perasTracer :: Tracer IO PerasLog
perasTracer = contramap (LT.unpack . LE.decodeUtf8 . A.encode) stdoutTracer
