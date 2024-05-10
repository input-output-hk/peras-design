{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.QCD.Node.Conformance (
  RunMonad (..),
) where

import Control.Lens ((^.))
import Control.Monad.State (
  MonadState (get, put),
  MonadTrans (..),
  State,
  StateT (StateT),
  evalState,
  execState,
  gets,
  modify,
 )
import Peras.QCD.Node.Model (NodeModel (NodeModel), currentSlot, emptyNode, protocol)
import Peras.QCD.Protocol (Params (paramU))
import Peras.QCD.Types (Chain, Message, PartyId, Tx, Vote)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (Some), HasVariables (..), Realized, RunModel (perform, postcondition), StateModel (..))

import qualified Peras.QCD.Node.API as API (PerasNode (..))
import qualified Peras.QCD.Node.Specification as Specification (blockCreation, fetching, initialize, voting)

instance HasVariables NodeModel where
  getAllVariables = mempty

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    Initialize :: Params -> PartyId -> Action NodeModel [Message]
    Fetching :: [Chain] -> [Vote] -> Action NodeModel [Message]
    BlockCreation :: [Tx] -> Action NodeModel [Message]
    Voting :: Action NodeModel [Message]

  initialState = emptyNode

  nextState state action _var =
    case action of
      Initialize params party -> execState (Specification.initialize params party) state
      Fetching chains' votes' -> execState (Specification.fetching chains' votes') state
      BlockCreation txs -> execState (Specification.blockCreation txs) state
      Voting -> execState Specification.voting state

  precondition node =
    \case
      Initialize{} -> True
      Fetching{} -> True
      BlockCreation{} -> True
      Voting{} -> (node ^. currentSlot) `mod` paramU (node ^. protocol) == 0

  arbitraryAction _context NodeModel{} = undefined -- FIXME: To be implemented.

deriving instance Show (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables = mempty

newtype RunMonad n m a = RunMonad {runMonad :: StateT n m a}
  deriving newtype (Functor, Applicative, Monad, MonadState n)

instance MonadTrans (RunMonad n) where
  lift = RunMonad . lift

type instance Realized (RunMonad n m) [Message] = [Message]

instance (Monad m, API.PerasNode n m) => RunModel NodeModel (RunMonad n m) where
  perform _state (Initialize params party) _context = apply $ API.initialize params party
  perform _state (Fetching chains' votes') _context = apply $ API.fetching chains' votes'
  perform _state (BlockCreation txs) _context = apply $ API.blockCreation txs
  perform _state Voting _context = apply API.voting

  postcondition (prior, _) (Initialize params party) _env actual = check prior actual $ Specification.initialize params party
  postcondition (prior, _) (Fetching chains' votes') _env actual = check prior actual $ Specification.fetching chains' votes'
  postcondition (prior, _) (BlockCreation txs) _env actual = check prior actual $ Specification.blockCreation txs
  postcondition (prior, _) Voting _env actual = check prior actual Specification.voting

apply :: (Monad m, MonadTrans t, MonadState s (t m)) => (s -> m (a, s)) -> t m a
apply f = do
  (x, s') <- lift . f =<< get
  put s'
  pure x

check :: Monad m => s -> [Message] -> State s [Message] -> m Bool
check prior actual action =
  pure $ identical actual $ evalState action prior

identical :: [Message] -> [Message] -> Bool
identical x y =
  x == y || all (`elem` x) y && all (`elem` y) x
