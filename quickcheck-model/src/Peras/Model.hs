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

import Control.Monad (replicateM)
import Control.Monad.Reader (MonadReader, MonadTrans (..), ReaderT, asks)
import Data.ByteString (ByteString, unfoldr)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import System.Random (Random (random), RandomGen, mkStdGen, split)
import Test.QuickCheck (choose, elements, frequency)
import Test.QuickCheck.StateModel (Any (..), HasVariables, Realized, RunModel (..), StateModel (..))
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

newtype Slot = Slot {unSlot :: Natural}
  deriving newtype (Eq, Show, Num)

-- | We model a network of nodes interconnected through a diffusion layer.
data Network = Network
  { nodeIds :: [NodeId]
  , slot :: Slot
  }
  deriving (Show, Generic)

newtype BlockId = BlockId {unBlockId :: ByteString}
  deriving (Eq, Show, Ord, Generic)

newtype NodeId = NodeId {unNodeId :: ByteString}
  deriving (Eq, Show, Ord, Generic)

baseNodes :: (RandomGen g) => g -> [NodeId]
baseNodes g =
  take 10 $ NodeId <$> List.unfoldr (Just . genNodeId) g
 where
  genNodeId seed =
    let (g1, g2) = split seed
     in (unfoldr (Just . random) g1, g2)

data Block = Block
  { blockId :: BlockId
  , producer :: NodeId
  , previousBlock :: BlockId
  }
  deriving (Eq, Show, Ord, Generic)

data Chain
  = Genesis
  | Chain Block Chain
  deriving (Eq, Show, Generic)

instance StateModel Network where
  data Action Network a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action Network (Set Block)
    -- Observe a node's best chain
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

-- | Messages sent to the node.
data Input
  = -- | New slot occurs (represents the passage of time)
    NextSlot Slot
  | -- | Some `NodeId` has sent a requested `Block` to this node.
    SomeBlock NodeId Block
  | -- | Some `NodeId` is notifying us their best chain has changed.
    UpdatedChain NodeId Chain

data Output
  = -- | Node needs some block from given `NodeId`.
    FetchBlock NodeId Block
  | -- | Node changed its best chain
    NewChain Chain

-- | Basic interface to a `Node` instance.
data Node m = Node
  { nodeId :: NodeId
  , step :: Input -> m [Output]
  -- ^ Nodes are assumed to progress in steps
  , inbox :: [(Slot, Input)]
  -- ^ New inputs to be delivered to the node at some `Slot`
  }

-- | All known nodes in the network.
-- FIXME: Atm we assume fully connected topology, this will evolve as we refine the model.
data Nodes m = Nodes
  { nodes :: Map.Map NodeId (Node m)
  }

newtype RunMonad m a = RunMonad {runMonad :: ReaderT (Nodes m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadReader (Nodes m))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) a = a

instance (Monad m) => RunModel Network (RunMonad m) where
  perform network@Network{slot} action _context =
    case action of
      Tick n ->
        Set.fromList . mconcat <$> replicateM (fromIntegral n) performTick
      ObserveBestChain nodeId ->
        currentChain nodeId
   where
    performTick :: RunMonad m [Block]
    performTick = do
      nodes <- asks $ Map.elems . nodes
      selectBlocks . mconcat <$> lift (traverse tick nodes)

    tick Node{step} = step (NextSlot slot)

    currentChain _nodeId = undefined

selectBlocks :: [Output] -> [Block]
selectBlocks = Data.Maybe.mapMaybe isBlockForged

isBlockForged :: Output -> Maybe Block
isBlockForged = \case
  NewChain{} -> Nothing
