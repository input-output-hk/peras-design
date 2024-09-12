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
import Data.Maybe (fromJust, isJust)
import Data.Set (Set)
import Peras.Block (Block (certificate))
import Peras.Chain (Chain, Vote)
import Peras.Conformance.Model (
  EnvAction (BadVote, NewChain, NewVote, Tick),
  NodeModel (..),
  checkVotingRules,
  pref,
  transition,
  vr1A,
  vr1B,
  vr2A,
  vr2B,
 )
import Peras.Conformance.Test (Action (Step), backoff, modelSUT)
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
  classify,
  counterexample,
  ioProperty,
  noShrinking,
  tabulate,
  whenFail,
 )
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

instance (Realized m ([Chain], [Vote]) ~ ([Chain], [Vote]), MonadSTM m) => RunModel NodeModel (Runtime m) where
  perform NodeModel{..} (Step a) _ = case a of
    Tick -> do
      RunState{..} <- get
      modify $ \rs -> rs{unfetchedChains = mempty, unfetchedVotes = mempty}
      lift $ do
        let clock' = clock + 1
            txs = []
        _ <- fetching tracer protocol modelSUT stateVar clock' unfetchedChains unfetchedVotes
        _ <- blockCreation tracer protocol modelSUT stateVar clock' txs (diffuseChain diffuserVar)
        let roundNumber = inRound clock' protocol
            party = mkCommitteeMember modelSUT protocol clock' (isCommitteeMember modelSUT roundNumber)
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
    BadVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty

  postcondition (s, s') (Step a) _ (gotChains, gotVotes) = do
    monitorPost $ tabulate "Voting rules" [show $ checkVotingRules $ backoff s]
    monitorPost $ tabulate "VR-1A/1B/2A/2B" [init . tail $ show (vr1A s'', vr1B s'', vr2A s'', vr2B s'') | let s'' = backoff s]
    monitorPost $ tabulate "Chain length (rounded)" [show $ (+ 5) . (* 10) . (`div` 10) . (+ 4) $ length $ pref s]
    monitorPost $ tabulate "Certs on chain" [show $ length $ filter (isJust . certificate) $ pref s]
    monitorPost $ tabulate "Certs created (rounded)" [show $ (* 2) . (`div` 2) $ length $ allSeenCerts s]
    let (expectedChains, expectedVotes) = maybe (mempty, mempty) fst (transition s a)
    -- let ok = length r == length expected
    let ok = (gotChains, gotVotes) == (expectedChains, expectedVotes)
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $
        "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (null gotChains) $ do
      monitorPost . counterexample . show $ "  --      got chains:" <+> pPrint gotChains
    when (gotChains /= expectedChains) $
      counterexamplePost . show $
        "  -- expected chains:" <+> pPrint expectedChains
    unless (null gotVotes) $ do
      monitorPost . counterexample . show $ "  --      got votes:" <+> pPrint gotVotes
    when (gotVotes /= expectedVotes) $
      counterexamplePost . show $
        "  -- expected votes:" <+> pPrint expectedVotes
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
