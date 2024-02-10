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

module Peras.Model where

import Control.Monad.State (MonadState, StateT, gets, modify)
import Control.Monad.Trans (MonadTrans (..))
import qualified Data.ByteString.Lazy as LBS
import Data.Default (def)
import Data.Either (partitionEithers)
import Data.Foldable (traverse_)
import qualified Data.List as List
import qualified Data.Map as Map
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Message (Message (..), NodeId (..))
import Peras.RandomForks.Types (Parameters, activeSlotCoefficient)
import System.Random (Random (random), RandomGen, mkStdGen, split)
import Test.QuickCheck (choose, elements, frequency)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (..), HasVariables, Realized, RunModel (..), StateModel (..))
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- | We model a network of nodes interconnected through a diffusion layer.
data Network = Network
  { nodeIds :: [NodeId]
  , slot :: Slot
  , parameters :: Parameters
  }
  deriving (Show, Generic)

instance DynLogicModel Network

baseNodes :: (RandomGen g) => g -> [NodeId]
baseNodes g =
  take 10 $ NodeId <$> List.unfoldr (Just . genNodeId) g
  where
    genNodeId seed =
      let (g1, g2) = split seed
       in (LBS.toStrict $ LBS.take 32 $ LBS.unfoldr (Just . random) g1, g2)

data Chain
  = Genesis
  | Chain (Block ()) Chain
  deriving (Eq, Show, Generic)

asList :: Chain -> [Block ()]
asList = List.unfoldr $ \case
  Genesis -> Nothing
  Chain b c -> Just (b, c)

instance StateModel Network where
  data Action Network a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action Network ()
    -- Observe a node's best chain at some point in time
    ObserveBestChain :: NodeId -> Action Network Chain

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
      , parameters = def
      }

  nextState currentState@Network{slot} action _var =
    case action of
      Tick n -> currentState{slot = slot + fromIntegral n}
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
  -- ^ Deliver some messages to this node
  , step :: m [Message ()]
  -- ^ Nodes are assumed to progress in steps
  , inbox :: [(Slot, Message ())]
  -- ^ New inputs to be delivered to the node at some `Slot`
  , bestChain :: m Chain
  -- ^ What's this node current best chain?
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

instance (Monad m) => RunModel Network (RunMonad m) where
  perform Network{slot} action _context =
    case action of
      Tick n ->
        performTick n
      ObserveBestChain nodeId ->
        currentChain nodeId
    where
      performTick :: Natural -> RunMonad m ()
      performTick n
        | n == 0 = pure ()
        | otherwise = do
            allNodes <- gets (Map.elems . nodes)
            traverse_ tick allNodes
            performTick (n - 1)

      tick :: Node m -> RunMonad m [Message ()]
      tick node@Node{nodeId, step, deliver, inbox} = do
        let (pending, deliverables) = partitionEithers $ map (deliverableAt slot) inbox
        -- deliver all messages in inbox
        mapM_ (lift . deliver) deliverables
        -- update the node's state
        modify $ Nodes . Map.insert nodeId (node{inbox = pending}) . nodes
        -- then let the node advance one slot and return the messages it sends
        lift step

      currentChain :: NodeId -> RunMonad m Chain
      currentChain nodeId =
        gets (Map.lookup nodeId . nodes)
          >>= maybe (error $ "Invalid node id:" <> show nodeId) (lift . bestChain)

  postcondition (_, Network{slot, parameters}) ObserveBestChain{} _env value =
    -- node has at least slot / f blocks
    pure $
      fromIntegral (length (asList value))
        >= (fromIntegral (toInteger slot) / activeSlotCoefficient parameters)
  postcondition _ _ _ _ = pure True

deliverableAt :: Slot -> (Slot, a) -> Either (Slot, a) a
deliverableAt at m@(delay, msg) =
  if at >= delay
    then Right msg
    else Left m
