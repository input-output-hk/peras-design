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

-- | A very simplistic and early stage model for a Praos/Peras nodes network.
-- FIXME: unused for now
module Peras.NetworkModel where

import Control.Monad (replicateM)
import Control.Monad.State (MonadState, StateT, gets, modify)
import Control.Monad.Trans (MonadTrans (..))
import Data.Either (partitionEithers)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain)
import Peras.Message (Message (..), NodeId (..))
import Peras.Orphans ()
import System.Random (RandomGen, mkStdGen)
import Test.QuickCheck (choose, elements, frequency)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (..), HasVariables, Realized, RunModel (..), StateModel (..))
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- | We model a network of nodes interconnected through a diffusion layer.
data Network = Network
  { nodeIds :: [NodeId]
  , slot :: Slot
  }
  deriving (Show, Generic)

instance DynLogicModel Network

baseNodes :: RandomGen g => g -> [NodeId]
baseNodes g =
  take 10 $ MkNodeId . ("N" <>) . show <$> [1 .. 10]

instance StateModel Network where
  data Action Network a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action Network (Set (Block ()))
    -- Observe a node's best chain
    ObserveBestChain :: NodeId -> Action Network (Chain ())

  arbitraryAction _ Network{nodeIds} =
    frequency
      [ (10, Some . Tick . fromInteger <$> choose (1, 100))
      , (1, observeNode)
      ]
   where
    observeNode = Some . ObserveBestChain <$> elements nodeIds

  initialState =
    Network
      { nodeIds = baseNodes (mkStdGen 42)
      , slot = 0
      }

  nextState currentState@Network{slot} action _var =
    case action of
      Tick n -> currentState{slot = slot + 1}
      ObserveBestChain{} -> currentState

deriving instance Eq (Action Network a)
deriving instance Show (Action Network a)

instance HasVariables Network where
  getAllVariables = const mempty

instance HasVariables (Action Network a) where
  getAllVariables = const mempty

-- | Basic interface to a `Node` instance.
data Node m = Node
  { nodeId :: NodeId
  , deliver :: Message () -> m ()
  , step :: m [Message ()]
  -- ^ Nodes are assumed to progress in steps
  , inbox :: [(Slot, Message ())]
  -- ^ New inputs to be delivered to the node at some `Slot`
  , bestChain :: m (Chain ())
  }

-- | All known nodes in the network.
-- FIXME: Atm we assume fully connected topology, this will evolve as we refine the model.
data Nodes m = Nodes
  { nodes :: Map.Map NodeId (Node m)
  }

newtype RunMonad m a = RunMonad {runMonad :: StateT (Nodes m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadState (Nodes m))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) a = a

instance Monad m => RunModel Network (RunMonad m) where
  perform network@Network{slot} action _context =
    case action of
      Tick n ->
        Set.fromList . mconcat <$> replicateM (fromIntegral n) performTick
      ObserveBestChain nodeId ->
        currentChain nodeId
   where
    performTick :: RunMonad m [Block ()]
    performTick = do
      allNodes <- gets (Map.elems . nodes)
      selectBlocks . mconcat <$> traverse tick allNodes

    tick :: Node m -> RunMonad m [Message ()]
    tick node@Node{nodeId, step, deliver, inbox} = do
      let (pending, deliverables) = partitionEithers $ map (deliverableAt slot) inbox
      -- deliver all messages in inbox
      mapM_ (lift . deliver) deliverables
      -- update the node's state
      modify $ Nodes . Map.insert nodeId (node{inbox = pending}) . nodes
      -- then let the node advance one slot and return the messages it sends
      lift step

    currentChain :: NodeId -> RunMonad m (Chain ())
    currentChain nodeId =
      gets (Map.lookup nodeId . nodes)
        >>= maybe (error $ "Invalid node id:" <> show nodeId) (lift . bestChain)

selectBlocks :: [Message ()] -> [Block ()]
selectBlocks = mapMaybe $ \case
  SomeBlock b -> Just b
  _other -> Nothing

deliverableAt :: Slot -> (Slot, a) -> Either (Slot, a) a
deliverableAt at m@(delay, msg) =
  if at >= delay
    then Right msg
    else Left m
