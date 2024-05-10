{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.QCD.Node.Impl.Perfect (
  PerfectNode,
) where

import Control.Monad.State (runState)
import Data.Default (Default (..))
import Peras.QCD.Node.API (PerasNode (..))

import qualified Peras.QCD.Node.Model as Specification (NodeModel, emptyNode)
import qualified Peras.QCD.Node.Specification as Specification (blockCreation, fetching, initialize, voting)

type PerfectNode = Specification.NodeModel

instance Default PerfectNode where
  def = Specification.emptyNode

instance Monad m => PerasNode PerfectNode m where
  initialize params party = pure . runState (Specification.initialize params party)
  fetching chains votes = pure . runState (Specification.fetching chains votes)
  blockCreation txs = pure . runState (Specification.blockCreation txs)
  voting weight = pure . runState (Specification.voting weight)
