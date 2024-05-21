{-# LANGUAGE DeriveGeneric #-}

module Peras.SmallStep.Experiment.Types where

import Peras.Chain (Chain)

import GHC.Generics (Generic)
import Peras.Orphans ()

newtype NodeState = MkNodeState {preferredChain :: Chain}
  deriving (Eq, Generic, Show)

data NodeTransition a = MkNodeTransition
  { output :: a
  , final :: NodeState
  }
  deriving (Eq, Generic, Show)

newtype Act = NewChain Chain
  deriving (Eq, Generic, Show)

data Query
  = QueryChain
  | QueryWeight
  deriving (Eq, Generic, Show)

data Signal
  = Transition Act
  | Observe Query
  deriving (Eq, Generic, Show)

data Response
  = UnitResponse
  | BoolResponse Bool
  | NatResponse Integer
  | ChainResponse Chain
  deriving (Eq, Generic, Show)
