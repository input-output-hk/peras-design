{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | A simple and early stage model for a Praos/Peras node and its environment.
module Peras.NodeModel where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically, readTQueue, writeTQueue)
import Control.Monad (forM)
import Control.Monad.Class.MonadFork (ThreadId)
import Control.Monad.Reader (MonadReader, ReaderT, ask, asks)
import Control.Monad.Trans (MonadTrans (..))
import qualified Data.Set as Set
import Data.Statistics.Util (equalsBinomialWithinTails)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain (..))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), OutMessage (..))
import Peras.IOSim.Node (NodeProcess (..))
import Peras.IOSim.Types (Votes)
import Peras.Message (Message (..), NodeId (..))
import Test.QuickCheck (choose, tabulate)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (..), HasVariables, PostconditionM, Realized, RunModel (..), StateModel (..), Var, counterexamplePost, monitorPost)
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- | A simple model of time passing and forged blocks
data NodeModel = NodeModel
  { forgedBlocks :: [Var [Block Votes]]
  -- ^ List of forged blocks references as observed from the node's behaviour
  , slot :: Slot
  }
  deriving (Show, Generic)

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action NodeModel [Block Votes]
    ForgedBlocksRespectSchedule :: [Var [Block Votes]] -> Action NodeModel Rational

  arbitraryAction _ NodeModel{} =
    Some . Tick . fromInteger <$> choose (500, 2000)

  initialState =
    NodeModel
      { forgedBlocks = []
      , slot = 0
      }

  nextState currentState@NodeModel{forgedBlocks, slot} action var =
    case action of
      Tick n ->
        currentState
          { forgedBlocks = var : forgedBlocks
          , slot = slot + n
          }
      ForgedBlocksRespectSchedule{} -> currentState

deriving instance Eq (Action NodeModel a)
deriving instance Show (Action NodeModel a)

instance HasVariables NodeModel where
  getAllVariables NodeModel{forgedBlocks} = Set.fromList $ Some <$> forgedBlocks

instance HasVariables (Action NodeModel a) where
  getAllVariables = \case
    ForgedBlocksRespectSchedule blockVars -> Set.fromList $ Some <$> blockVars
    _other -> mempty

-- | Basic interface to a single node instance.
data Node m = Node
  { nodeId :: NodeId
  , nodeThreadId :: ThreadId m
  , nodeProcess :: NodeProcess m
  , -- FIXME: these types link the `Node` representation to what's defined in peras-iosim package
    -- which is not desirable, define own "test" interface
    -- or better yet, define an interface in Agda?
    nodeStake :: Rational
  }

defaultActiveSlotCoefficient :: Double
defaultActiveSlotCoefficient = 0.1

newtype RunMonad m a = RunMonad {runMonad :: ReaderT (Node m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadReader (Node m))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) a = a

instance forall m. MonadSTM m => RunModel NodeModel (RunMonad m) where
  perform NodeModel{slot} action _context =
    case action of
      Tick n ->
        mconcat <$> forM [1 .. n] tick
      ForgedBlocksRespectSchedule{} -> asks nodeStake
   where
    tick :: Slot -> RunMonad m [Block Votes]
    tick k = do
      Node{nodeProcess = NodeProcess{incoming, outgoing}} <- ask
      -- tick the node
      lift $ do
        atomically $ writeTQueue incoming (InEnvelope Nothing $ NextSlot $ slot + k)
        -- collect outgoing messages until Idle
        atomically $ waitForIdle outgoing []

    waitForIdle q acc = do
      readTQueue q >>= \case
        Idle{} -> pure acc
        OutEnvelope
          { outMessage = SendMessage (NewChain (Cons b _))
          } -> waitForIdle q (b : acc)
        _other -> waitForIdle q acc

  postcondition (_before, NodeModel{slot}) (ForgedBlocksRespectSchedule blockVars) env stakeRatio | slot > 0 = do
    let blocks = length $ foldMap env blockVars
    produceExpectedNumberOfBlocks stakeRatio blocks slot
  postcondition _ _ _ _ = pure True

produceExpectedNumberOfBlocks :: Monad m => Rational -> Int -> Slot -> PostconditionM m Bool
produceExpectedNumberOfBlocks stakeRatio blocks slot =
  do
    let expectedBP :: Double = fromRational $ stakeRatio * toRational (fromIntegral slot * defaultActiveSlotCoefficient)
        actualBP = fromIntegral blocks
    counterexamplePost $ "Actual: " <> show blocks <> ", Expected:  " <> show expectedBP
    counterexamplePost $
      "Stake: "
        <> show stakeRatio
        <> ", active slots: "
        <> show defaultActiveSlotCoefficient
        <> ", Slot: "
        <> show slot
    monitorPost $ tabulate "# Blocks" ["<= " <> show ((blocks `div` 100 + 1) * 100)]
    pure $
      equalsBinomialWithinTails
        (fromIntegral slot) -- The sample size.
        (1 - (1 - defaultActiveSlotCoefficient) ** fromRational stakeRatio) -- Praos probability.
        3 -- Three standard deviations corresponds to the confidence interval from 0.3% to 99.7%.
        -- That means that the test will fail after a few batches of 100 tests.
        actualBP
