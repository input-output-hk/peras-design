{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | A very simplistic and early stage model for a Praos/Peras nodes network.
-- FIXME: unused for now
module Peras.NetworkModel where

import Control.Monad (replicateM_)
import Control.Monad.Reader (MonadReader, ReaderT, ask)
import Control.Monad.Trans (MonadTrans (..))
import Data.Maybe (mapMaybe)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Chain, asChain, asList)
import Peras.Message (Message (..), NodeId (..))
import Peras.Orphans ()
import Test.QuickCheck (choose, elements, frequency, tabulate)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (..), HasVariables, LookUp, PostconditionM, Realized, RunModel (..), StateModel (..), Var, counterexamplePost, monitorPost)
import Test.QuickCheck.StateModel.Variables (HasVariables (..))

-- | We model a network of nodes interconnected through a diffusion layer.
data Network = Network
  { nodeIds :: [NodeId]
  , slot :: Slot
  }
  deriving (Show, Generic)

instance DynLogicModel Network

baseNodes :: Int -> [NodeId]
baseNodes n =
  MkNodeId . ("N" <>) . show <$> [1 .. n]

instance StateModel Network where
  data Action Network a where
    -- Advance the time one or more slots possibly producing blocks.
    Tick :: Natural -> Action Network ()
    -- Observe a node's best chain
    ObserveBestChain :: NodeId -> Action Network (Chain ())
    -- Ensure chains have a common prefix
    ChainsHaveCommonPrefix :: [Var (Chain ())] -> Action Network ()

  arbitraryAction _ Network{nodeIds} =
    frequency
      [ (10, Some . Tick . fromInteger <$> choose (10, 200))
      , (1, observeNode)
      ]
   where
    observeNode = Some . ObserveBestChain <$> elements nodeIds

  initialState =
    Network
      { nodeIds = baseNodes 10
      , slot = 0
      }

  nextState currentState@Network{slot} action _var =
    case action of
      Tick n -> currentState{slot = slot + n}
      ObserveBestChain{} -> currentState
      ChainsHaveCommonPrefix{} -> currentState

deriving instance Eq (Action Network a)
deriving instance Show (Action Network a)

instance HasVariables Network where
  getAllVariables = const mempty

instance HasVariables (Action Network a) where
  getAllVariables = const mempty

-- | An interface to a  simulator for a network
data Simulator m = Simulator
  { step :: m ()
  -- ^ Step the network one slot
  , preferredChain :: NodeId -> m (Chain ())
  -- ^ Return preferred chain for a specific node in the network.
  , stop :: m ()
  -- ^ Stop all nodes in the network
  }

newtype RunMonad m a = RunMonad {runMonad :: ReaderT (Simulator m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadReader (Simulator m))

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) a = a

instance Monad m => RunModel Network (RunMonad m) where
  perform network@Network{slot} action _context =
    case action of
      Tick n ->
        replicateM_ (fromIntegral n) performTick
      ObserveBestChain nodeId ->
        currentChain nodeId
      ChainsHaveCommonPrefix{} ->
        pure ()
   where
    performTick :: RunMonad m ()
    performTick =
      ask >>= lift . step

    currentChain :: NodeId -> RunMonad m (Chain ())
    currentChain nodeId =
      ask
        >>= lift . flip preferredChain nodeId

  postcondition ::
    Monad m =>
    (Network, Network) ->
    Action Network a ->
    LookUp (RunMonad m) ->
    Realized (RunMonad m) a ->
    PostconditionM (RunMonad m) Bool
  postcondition (_, Network{slot}) (ChainsHaveCommonPrefix chainVars) env () = do
    let chains = fmap env chainVars
        prefix = commonPrefix chains
    counterexamplePost $ "Chains:  " <> show chains
    counterexamplePost $ "Common prefix:  " <> show prefix
    monitorPost $ tabulate "Prefix length" ["<= " <> show ((length (asList prefix) `div` 100 + 1) * 100)]
    pure $ not (null (asList prefix))
  postcondition _ _ _ _ = pure True

commonPrefix :: [Chain ()] -> Chain ()
commonPrefix chains =
  asChain . reverse $ foldl1 prefix blocks
 where
  blocks = reverse . asList <$> chains

  prefix :: [Block ()] -> [Block ()] -> [Block ()]
  prefix (a : as) (b : bs)
    | a == b = a : prefix as bs
  prefix _ _ = []

selectBlocks :: [Message ()] -> [Block ()]
selectBlocks = mapMaybe $ \case
  SomeBlock b -> Just b
  _other -> Nothing

deliverableAt :: Slot -> (Slot, a) -> Either (Slot, a) a
deliverableAt at m@(delay, msg) =
  if at >= delay
    then Right msg
    else Left m
