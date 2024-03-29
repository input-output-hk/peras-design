{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | A simple and early stage model for a Praos/Peras node and its environment.
module Peras.OptimalModel where

import Control.Monad (forM)
import Control.Monad.Class.MonadTime (addUTCTime)
import Control.Monad.Reader (MonadReader, ReaderT, ask, asks)
import Control.Monad.State
import Control.Monad.Trans (MonadTrans (..))
import qualified Data.Aeson as A
import Data.Function (on)
import qualified Data.Set as Set
import Data.Statistics.Util (equalsBinomialWithinTails)
import qualified Data.Text.Lazy as LT
import Data.Text.Lazy.Encoding (decodeUtf8)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain)
import Peras.Event (UniqueId (UniqueId))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..))
import Peras.IOSim.Node.Types
import Peras.IOSim.Types (simulationStart)
import Peras.Message (Message (..), NodeId (..))
import Peras.Orphans ()
import Test.QuickCheck (arbitrary, choose, frequency, tabulate)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel -- (Any (..), HasVariables, PostconditionM, Realized, RunModel (..), StateModel (..), Var, counterexamplePost, monitorPost, Env(..))
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- 1. state of the model to generate actions and traces
-- 2. need interesting actions
-- 3. define for each action
--     1. generator for action from state
--     2. transition function
--     3. precondition, often similar to generator (don't violate precondition)
--     4. (maybe) shrinkers
--     5. (later) negative preconditions
-- 4. run model
--     1. initial state
--     2. what each action does on the actual system under test ("perform")
--     3. postconditions (expected results)
-- 5. initially just "local" behavior of node with mock environment
-- 6. (later) global properties with multiple interacting nodes

data Protocol = Peras

data NodeModel = NodeModel
  { preferredChain :: [Var Block]
  , preferredWeight :: Double
  }
  deriving (Eq, Show)

instance HasVariables NodeModel where
  getAllVariables = mempty

instance HasVariables (Action NodeModel a) where
  getAllVariables = mempty

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    Tick :: Action NodeModel ()
    LeadSlot :: Action NodeModel Block
    ReceiveChain :: [Block] -> Action NodeModel (Maybe Chain)

  arbitraryAction context NodeModel{preferredChain} =
    frequency
      [ (3, pure $ Some Tick)
      , (1, pure $ Some LeadSlot)
      , (1, Some . ReceiveChain . (: preferredChain) <$> arbitraryVar context)
      , (1, Some . ReceiveChain . (<> preferredChain) <$> arbitraryVar context)
      , (1, Some . ReceiveChain <$> arbitrary)
      ]

  initialState = NodeModel []

  nextState state@NodeModel{..} action var =
    case action of
      Tick -> state
      LeadSlot ->
        NodeModel
          { preferredChain = var : preferredChain
          , preferredWeight = 1 + preferredWeight
          }
      ReceiveChain chain ->
        -- FIXME: This is definitely not the correct way to
        -- do this, but how can we update the state using
        -- `var` if we cannot look it up in the environment?
        if on (>) chainLength chain (preferredChain state)
          then NodeModel chain
          else state

deriving instance Eq (Action NodeModel a)
deriving instance Show (Action NodeModel a)

chainLength :: Chain -> Double
chainLength = fromIntegral . length

instance (Monad m, PerasNode n) => RunModel NodeModel (StateT n m) where
  perform _state Tick _lookup = undefined

{-
optimal : ∀ (c : Chain) (t : tT) (sl : Slot)
  → let b = bestChain sl t
    in
    ValidChain {block₀} {IsSlotLeader} {IsBlockSignature} c
  → c ⊆ allBlocksUpTo sl t
  → ∥ c , certs t c ∥ ≤ ∥ b , certs t b ∥
-}
