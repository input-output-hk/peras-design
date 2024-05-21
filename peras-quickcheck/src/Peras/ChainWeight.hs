{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.ChainWeight (
  BuggyNode,
  PerasNode,
  PerfectNode,
  RunMonad (..),
  Action (..),
) where

import Control.Monad.State (
  MonadState (get, put),
  MonadTrans,
  StateT (StateT),
  lift,
 )
import Data.Default (Default (..))
import Peras.Arbitraries ()
import Peras.Chain (Chain)
import Peras.SmallStep.Experiment.Types (Act (..), NodeState (MkNodeState), NodeTransition (..), Query (..), Response (..), Signal (..))
import Test.QuickCheck (arbitrary, frequency)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (Some), HasVariables (..), Realized, RunModel (perform, postcondition), StateModel (..))

import qualified Peras.SmallStep.Experiment as ES (nextState)

-- State model

instance HasVariables NodeState where
  getAllVariables = mempty

instance DynLogicModel NodeState

instance StateModel NodeState where
  data Action NodeState a where
    MkAction :: Signal -> Action NodeState Response
  initialState = MkNodeState mempty
  nextState state (MkAction signal) _var = final $ ES.nextState signal state
  arbitraryAction _context _state =
    frequency
      [ (8, Some . MkAction . Transition . NewChain <$> arbitrary)
      , (1, pure . Some . MkAction $ Observe QueryChain)
      , (1, pure . Some . MkAction $ Observe QueryWeight)
      ]

deriving instance Eq (Action NodeState a)
deriving instance Show (Action NodeState a)

instance HasVariables (Action NodeState a) where
  getAllVariables = mempty

-- Run model

class Monad m => PerasNode a m where
  newChain :: Chain -> a -> m (Bool, a)
  observeChain :: a -> m Chain
  observeWeight :: a -> m Integer
  observeWeight = fmap (toInteger . length) . observeChain

newtype RunMonad n m a = RunMonad {runMonad :: StateT n m a}
  deriving newtype (Functor, Applicative, Monad, MonadState n)

type instance Realized (RunMonad n m) Response = Response

instance MonadTrans (RunMonad n) where
  lift = RunMonad . lift

instance (Monad m, PerasNode n m) => RunModel NodeState (RunMonad n m) where
  perform _state (MkAction (Transition (NewChain chain))) _context = BoolResponse <$> apply (newChain chain)
  perform _state (MkAction (Observe QueryChain)) _context = ChainResponse <$> apply' observeChain
  perform _state (MkAction (Observe QueryWeight)) _context = NatResponse <$> apply' observeWeight
  postcondition (prior, _) (MkAction signal) _env actual =
    pure $ actual == output (ES.nextState signal prior)

apply :: (Monad m, MonadTrans t, MonadState s (t m)) => (s -> m (a, s)) -> t m a
apply f = do
  (x, s') <- lift . f =<< get
  put s'
  pure x

apply' :: (Monad m, MonadTrans t, MonadState s (t m)) => (s -> m a) -> t m a
apply' f = do
  s <- get
  x <- lift $ f s
  pure x

-- Examples

newtype PerfectNode = MkPerfectNode {preferredChain :: Chain}
  deriving (Eq, Show)

instance Default PerfectNode where
  def = MkPerfectNode mempty

instance Monad m => PerasNode PerfectNode m where
  newChain chain node
    | length chain > length (preferredChain node) = pure (True, MkPerfectNode chain)
    | otherwise = pure (False, node)
  observeChain = pure . preferredChain

newtype BuggyNode = MkBuggyNode {preferredChain' :: Chain}
  deriving (Eq, Show)

instance Default BuggyNode where
  def = MkBuggyNode mempty

instance Monad m => PerasNode BuggyNode m where
  newChain chain node
    | length chain `mod` 20 == 0 = pure (False, MkBuggyNode $ drop 1 chain)
    | length chain >= length (preferredChain' node) && length chain > 3 = pure (True, MkBuggyNode chain)
    | length chain > length (preferredChain' node) = pure (True, MkBuggyNode chain)
    | otherwise = pure (False, node)
  observeChain = pure . preferredChain'
