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
import Peras.Chain (Chain, Vote)
import Peras.Conformance.Model (
  EnvAction (..),
  NodeModel (..),
  transition,
 )
import Peras.Conformance.Test (
  Action (Initial, Step),
  NetworkModel (NetworkModel, nodeModel),
  modelSUT,
  monitorCerts,
  monitorChain,
  monitorVoting,
  sortition,
 )
import Peras.Numbering (RoundNumber (getRoundNumber))
import Peras.Prototype.BlockCreation (blockCreation)
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (
  isCommitteeMember,
  mkCommitteeMember,
 )
import Peras.Prototype.Diffusion (
  Diffuser,
  diffuseChain,
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
 )
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

instance (Realized m () ~ (), Realized m ([Chain], [Vote]) ~ ([Chain], [Vote]), MonadSTM m) => RunModel NetworkModel (Runtime m) where
  perform _ Initial{} _ = pure ()
  perform net@NetworkModel{nodeModel = NodeModel{..}} (Step a) _ = case a of
    Tick -> do
      RunState{..} <- get
      modify $ \rs -> rs{unfetchedChains = mempty, unfetchedVotes = mempty}
      lift $ do
        let clock' = clock + 1
            txs = []
            sut = modelSUT net
        _ <- fetching tracer protocol sut stateVar clock' unfetchedChains unfetchedVotes
        _ <- blockCreation tracer protocol sut stateVar clock' txs (diffuseChain diffuserVar)
        let roundNumber = inRound clock' protocol
            party = mkCommitteeMember sut protocol clock' (isCommitteeMember sut roundNumber)
            selectBlock' = selectBlock nullTracer
            diffuser = diffuseVote diffuserVar
        _ <- voting tracer protocol party stateVar clock' selectBlock' diffuser
        popChainsAndVotes diffuserVar clock'
    NewChain c -> do
      modify $ \rs -> rs{unfetchedChains = unfetchedChains rs ++ pure c}
      pure mempty
    NewVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty
    BadChain c -> do
      modify $ \rs -> rs{unfetchedChains = unfetchedChains rs ++ pure c}
      pure mempty
    BadVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty

  postcondition _ Initial{} _ () = pure True
  postcondition (net@NetworkModel{nodeModel = s}, net'@NetworkModel{nodeModel = s'}) (Step a) _ (gotChains, gotVotes) = do
    monitorChain net net'
    monitorCerts net net'
    monitorVoting net a
    let (expectedChains, expectedVotes) = maybe (mempty, mempty) fst (transition (sortition net) s a)
    let ok = (gotChains, gotVotes) == (expectedChains, expectedVotes)
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $
        "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (null gotChains) $
      monitorPost . counterexample . show $
        "  --      got chains:" <+> pPrint gotChains
    when (gotChains /= expectedChains) $
      counterexamplePost . show $
        "  -- expected chains:" <+> pPrint expectedChains
    unless (null gotVotes) $
      monitorPost . counterexample . show $
        "  --      got votes:" <+> pPrint gotVotes
    when (gotVotes /= expectedVotes) $
      counterexamplePost . show $
        "  -- expected votes:" <+> pPrint expectedVotes
    counterexamplePost . show $ "  " <> hang "-- model state before:" 2 (pPrint net)
    pure ok

prop_node :: Blind (Actions NetworkModel) -> Property
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
