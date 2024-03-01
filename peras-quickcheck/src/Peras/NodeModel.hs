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

import Control.Monad (forM)
import Control.Monad.Reader (MonadReader, ReaderT, ask, asks)
import Control.Monad.Trans (MonadTrans (..))
import qualified Data.Aeson as A
import qualified Data.Set as Set
import Data.Statistics.Util (equalsBinomialWithinTails)
import qualified Data.Text.Lazy as LT
import Data.Text.Lazy.Encoding (decodeUtf8)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain (..))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), OutMessage (..))
import Peras.Message (Message (..), NodeId (..))
import Test.QuickCheck (choose, tabulate)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (..), HasVariables, PostconditionM, Realized, RunModel (..), StateModel (..), Var, counterexamplePost, monitorPost)
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- | A simple model of time passing and forged blocks
data NodeModel = NodeModel
  { forgedBlocks :: [Var [Block]]
  -- ^ List of forged blocks references as observed from the node's behaviour
  , slot :: Slot
  }
  deriving (Show, Generic)

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action NodeModel [Block]
    ForgedBlocksRespectSchedule :: [Var [Block]] -> Action NodeModel Rational

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
          { forgedBlocks = forgedBlocks <> [var]
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
  , nodeStake :: Rational
  , sendMessage :: InEnvelope -> m ()
  , stopNode :: m ()
  , receiveMessage :: m OutEnvelope
  }

defaultActiveSlotCoefficient :: Double
defaultActiveSlotCoefficient = 0.1

newtype RunMonad m a = RunMonad {runMonad :: ReaderT (Node m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadReader (Node m))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) a = a

instance forall m. Monad m => RunModel NodeModel (RunMonad m) where
  perform NodeModel{slot} action _context =
    case action of
      Tick n ->
        mconcat <$> forM [1 .. n] tick
      ForgedBlocksRespectSchedule{} -> asks nodeStake
   where
    tick :: Slot -> RunMonad m [Block]
    tick k = do
      Node{sendMessage, receiveMessage} <- ask
      -- tick the node
      lift $ do
        sendMessage (InEnvelope Nothing $ NextSlot $ slot + k)
        -- collect outgoing messages until Idle
        waitForIdle receiveMessage []

    waitForIdle receive acc = do
      receive >>= \case
        Idle{} -> pure acc
        OutEnvelope
          { outMessage = SendMessage (NewChain (MkChain (b : _) _))
          } -> waitForIdle receive (b : acc)
        _other -> waitForIdle receive acc

  postcondition (_before, NodeModel{slot}) (ForgedBlocksRespectSchedule blockVars) env stakeRatio | slot > 0 = do
    let blocks = foldMap env blockVars
        numberOfBlocks = length blocks
    counterexamplePost $ "Chain: " <> LT.unpack (decodeUtf8 (A.encode blocks))
    produceExpectedNumberOfBlocks stakeRatio numberOfBlocks slot
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
    monitorPost $ tabulate "# Blocks" ["<= " <> show ((blocks `div` 1000 + 1) * 1000)]
    pure $
      equalsBinomialWithinTails
        (fromIntegral slot) -- The sample size.
        (1 - (1 - defaultActiveSlotCoefficient) ** fromRational stakeRatio) -- Praos probability.
        3 -- Three standard deviations corresponds to the confidence interval from 0.3% to 99.7%.
        -- That means that the test will fail after a few batches of 100 tests.
        actualBP
