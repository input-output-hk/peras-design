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

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically, newTQueueIO, readTQueue, writeTQueue)
import Control.Monad (forM, replicateM)
import Control.Monad.Class.MonadFork (MonadFork, ThreadId, forkIO)
import Control.Monad.Class.MonadTime (MonadTime, getCurrentTime)
import Control.Monad.Class.MonadTimer (MonadDelay)
import Control.Monad.Random (runRand)
import Control.Monad.Reader (MonadReader, ReaderT, ask)
import Control.Monad.Trans (MonadTrans (..))
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain (..))
import Peras.IOSim.Message.Types (InEnvelope (..), OutEnvelope (..), OutMessage (..))
import Peras.IOSim.Node (NodeProcess (..), initializeNode, runNode)
import Peras.IOSim.Protocol.Types (Protocol (..))
import Peras.IOSim.Simulate.Types (Parameters (..))
import Peras.Message (Message (..), NodeId (..))
import System.Random (mkStdGen)
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
  , nodeThreadId :: ThreadId m
  , nodeProcess :: NodeProcess () m
  }

initialiseNodeEnv ::
  ( MonadSTM m
  , MonadDelay m
  , MonadTime m
  , MonadFork m
  ) =>
  m (ThreadId m, NodeProcess () m)
initialiseNodeEnv = do
  let gen = mkStdGen 42
  now <- getCurrentTime
  nodeProcess <- NodeProcess <$> newTQueueIO <*> newTQueueIO
  let (nodeState, gen') = flip runRand gen $ initializeNode parameters now (MkNodeId "N1") (Set.singleton $ MkNodeId "N2")
  nodeThread <- forkIO $ runNode gen' parameters protocol nodeState nodeProcess
  pure (nodeThread, nodeProcess)

protocol :: Protocol
protocol = PseudoPraos 0.1

parameters :: Parameters
parameters =
  Parameters
    { randomSeed = 12345
    , peerCount = 10
    , downstreamCount = 3
    , maximumStake = 1000
    , endSlot = 1000
    , messageDelay = 0.35
    }

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
      ForgedBlocksRespectSchedule{} -> pure ()
   where
    tick :: Slot -> RunMonad m [Block ()]
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
          { timestamp
          , source
          , outMessage = SendMessage (NewChain (Cons b _))
          , bytes
          , destination
          } -> waitForIdle q (b : acc)
        other -> waitForIdle q acc
