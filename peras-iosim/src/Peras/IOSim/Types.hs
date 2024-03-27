{-# LANGUAGE DerivingStrategies #-}

module Peras.IOSim.Types (
  Coin,
  VoteWithBlock,
  simulationStart,
) where

import Control.Monad.Class.MonadTime (UTCTime)
import Peras.Block (Block)
import Peras.Chain (Vote)
import Peras.Orphans ()
import Test.QuickCheck.Instances.Natural ()

type Coin = Int

type VoteWithBlock = (Vote, Block)

simulationStart :: UTCTime
simulationStart = read "1970-01-01 00:00:00.0 UTC"
