{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | A simple and early stage model for a Praos/Peras node and its environment.
module Peras.NodeModel where

import Control.Concurrent.Class.MonadSTM (MonadSTM, newTQueueIO)
import Control.Monad.Reader (MonadReader, ReaderT)
import Control.Monad.Trans (MonadTrans (..))
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.IOSim.Node (NodeProcess (..))
import Peras.Message (NodeId (..))
import Test.QuickCheck (choose)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (..), HasVariables, Realized, RunModel (..), StateModel (..), Var)
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- | A simple model of time passing and forged blocks
data NodeModel = NodeModel
  { forgedBlocks :: [Var [Block ()]]
  -- ^ List of forged blocks references as observed from the node's behaviour
  , slot :: Slot
  }
  deriving (Show, Generic)

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action NodeModel [Block ()]
    ForgedBlocksRespectSchedule :: [Var [Block ()]] -> Action NodeModel ()

  arbitraryAction _ NodeModel{} =
    Some . Tick . fromInteger <$> choose (1, 100)

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
  getAllVariables = const mempty

-- | Basic interface to a `Peras.IOSim.Node` instance.
data Node m = Node
  { nodeId :: NodeId
  , nodeProcess :: NodeProcess () m
  }

initialiseNodeEnv :: MonadSTM m => m (NodeProcess () m)
initialiseNodeEnv =
  NodeProcess <$> newTQueueIO <*> newTQueueIO

newtype RunMonad m a = RunMonad {runMonad :: ReaderT (Node m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadReader (Node m))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) a = a

instance Monad m => RunModel NodeModel (RunMonad m) where
  perform NodeModel{} action _context =
    case action of
      Tick{} -> undefined
      ForgedBlocksRespectSchedule{} -> pure ()
