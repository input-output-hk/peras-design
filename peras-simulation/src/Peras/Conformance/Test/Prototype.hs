{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Peras.Conformance.Test.Prototype where

import Control.Concurrent.Class.MonadSTM (MonadSTM (TVar))
import Control.Concurrent.STM.TVar qualified as IO
import Control.Monad (unless, when)
import Control.Monad.State (
  MonadState (get),
  MonadTrans (lift),
  StateT,
  modify,
 )
import Control.Tracer (Tracer (Tracer), emit, nullTracer)
import Data.Default (Default (def))
import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.Maybe (fromJust)
import Data.Set (Set)
import Peras.Chain (Chain, Vote)
import Peras.Conformance.Model (
  EnvAction (BadVote, NewChain, NewVote, Tick),
  NodeModel (..),
  transition,
  checkVotingRules,)
import Peras.Conformance.Test (Action (Step), modelSUT)
import Peras.Numbering (RoundNumber (getRoundNumber))
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (
  isCommitteeMember,
  mkCommitteeMember,
 )
import Peras.Prototype.Diffusion (
  Diffuser,
  diffuseVote,
  popChainsAndVotes,
 )
import Peras.Prototype.Fetching (fetching)
import Peras.Prototype.Trace qualified as Trace
import Peras.Prototype.Types (
  PerasState,
  inRound,
  initialPerasState,
  newRound,
 )
import Peras.Prototype.Voting (voting)
import Test.QuickCheck (
  Blind (Blind),
  Property,
  counterexample,
  ioProperty,
  noShrinking,
  whenFail,
  classify,
  tabulate,)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.Extras (runPropertyStateT)
import Test.QuickCheck.Monadic (monadicIO, monitor)
import Test.QuickCheck.StateModel (
  Actions,
  Realized,
  RunModel (perform, postcondition),
  counterexamplePost,
  monitorPost,
  runActions,
 )
import Text.PrettyPrint (hang, vcat, (<+>))
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))
import Prelude hiding (round)

data RunState m = RunState
  { stateVar :: TVar m PerasState
  , diffuserVar :: TVar m Diffuser
  , tracer :: Tracer m Trace.PerasLog
  , unfetchedChains :: [Chain]
  , unfetchedVotes :: [Vote]
  }

type Runtime m = StateT (RunState m) m

instance (Realized m [Vote] ~ [Vote], MonadSTM m) => RunModel NodeModel (Runtime m) where
  perform NodeModel{..} (Step a) _ = case a of
    Tick -> do
      RunState{..} <- get
      modify $ \rs -> rs{unfetchedChains = mempty, unfetchedVotes = mempty}
      lift $ do
        let clock' = clock + 1
        -- TODO: also invoke blockCreation
        _ <- fetching tracer protocol modelSUT stateVar clock' unfetchedChains unfetchedVotes
        let roundNumber = inRound clock' protocol
            party = mkCommitteeMember modelSUT protocol clock' (isCommitteeMember modelSUT roundNumber)
            selectBlock' = selectBlock nullTracer
            diffuser = diffuseVote diffuserVar
        _ <- voting tracer protocol party stateVar clock' selectBlock' diffuser
        (cs, vs) <- popChainsAndVotes diffuserVar clock'
        pure vs
    NewChain c -> do
      modify $ \rs -> rs{unfetchedChains = unfetchedChains rs ++ pure c}
      pure mempty
    NewVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty
    BadVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty

  postcondition (s, s') (Step a) _ r = do
    monitorPost $ tabulate "votingRules" [show $ checkVotingRules s']
    let expected = fst (fromJust (transition s a))
    -- let ok = length r == length expected
    let ok = r == expected
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $
        "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (null r) $ do
      monitorPost . counterexample . show $ "  --      got:" <+> pPrint r
    counterexamplePost . show $ "  -- expected:" <+> pPrint expected
    counterexamplePost . show $ "  " <> hang "-- model state before:" 2 (pPrint s)
    pure ok

prop_node :: Blind (Actions NodeModel) -> Property
prop_node (Blind as) = noShrinking $
  ioProperty $ do
    stateVar <- IO.newTVarIO initialPerasState
    diffuserVar <- IO.newTVarIO def
    traceRef <- newIORef []
    let unfetchedChains = mempty
        unfetchedVotes = mempty
        tracer = Tracer $ emit $ \a -> modifyIORef traceRef (a :)
        printTrace = do
          putStrLn "-- Trace from node:"
          trace <- readIORef traceRef
          print $ vcat . map pPrint $ reverse trace
    pure $
      whenFail printTrace $
        monadicIO $ do
          monitor $ counterexample "-- Actions:"
          monitor $ counterexample "do"
          _ <- runPropertyStateT (runActions @_ @(Runtime IO) as) RunState{..}
          pure True