{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Prototype.Node.Model
where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (newTVarIO, readTVarIO),
 )
import Control.Monad.Except (
  ExceptT (ExceptT),
  MonadError (throwError),
  runExceptT,
 )
import Control.Monad.IOSim (runSim)
import Control.Monad.State (
  MonadState,
  MonadTrans,
  StateT (StateT),
  get,
  lift,
  modify',
 )
import Control.Tracer (nullTracer)
import Data.Default (Default (..))
import Data.Foldable (toList)
import Data.List ((\\))
import qualified Data.Map as Map
import Peras.Arbitraries ()
import Peras.Block (
  Block (MkBlock, creatorId, slotNumber),
  Certificate (MkCertificate, round),
  Party (MkParty, pid),
 )
import Peras.Chain (Chain, Vote (MkVote, creatorId, votingRound))
import Peras.Crypto (
  Hashable (hash),
  VerificationKey (MkVerificationKey),
 )
import Peras.Numbering (SlotNumber)
import Peras.Prototype.BlockCreation (blockCreation)
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (
  IsCommitteeMember,
  IsSlotLeader,
  mkCommitteeMember,
  mkParty,
  mkSlotLeader,
 )
import Peras.Prototype.Diffusion (
  defaultDiffuser,
  diffuseChain,
  diffuseVote,
  popChainsAndVotes,
 )
import Peras.Prototype.Fetching (fetching)
import Peras.Prototype.Types (
  Payload,
  PerasError (MultipleItemsDiffused),
  PerasParams,
  PerasState (..),
  hashTip,
  inRound,
  initialPerasState,
  newRound,
  systemStart,
 )
import Peras.Prototype.Voting (voting)
import Test.QuickCheck (arbitrary, elements, frequency, listOf, suchThat)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (Some), HasVariables (..), Realized, RunModel (perform, postcondition), StateModel (..))
import Prelude hiding (round)

data NodeModel = MkNodeModel
  { self :: Party
  , clock :: SlotNumber
  , protocol :: PerasParams
  , state :: PerasState
  }
  deriving (Eq, Show)

instance Default NodeModel where
  def =
    MkNodeModel
      { self = noParty
      , clock = systemStart
      , protocol = def
      , state = initialPerasState
      }

instance HasVariables NodeModel where
  getAllVariables = mempty

instance DynLogicModel NodeModel

noParty :: Party
noParty = MkParty 0 $ MkVerificationKey mempty

initialized :: NodeModel -> Bool
initialized MkNodeModel{self} = self /= noParty

fetched :: NodeModel -> Bool
fetched MkNodeModel{clock, protocol, state = MkPerasState{chains, votes}} =
  any (any (\MkBlock{slotNumber} -> slotNumber == clock)) chains
    && any (\MkVote{votingRound} -> votingRound == inRound clock protocol) votes

forged :: NodeModel -> Bool
forged MkNodeModel{self, clock, state = MkPerasState{chains}} =
  any
    ( any
        ( \MkBlock{slotNumber, creatorId} ->
            slotNumber /= clock || creatorId /= pid self
        )
    )
    chains

voted :: NodeModel -> Bool
voted MkNodeModel{self, clock, protocol, state = MkPerasState{votes}} =
  any
    ( \MkVote{votingRound, creatorId} ->
        votingRound /= inRound clock protocol || creatorId /= pid self
    )
    votes

-- FIXME: Replace with an executable specification generated from Agda.
initializeModeled :: Party -> SlotNumber -> PerasParams -> NodeModel -> ((), NodeModel)
initializeModeled party start params node = ((), node{self = party, clock = start, protocol = params})

-- FIXME: Replace with an executable specification generated from Agda.
tickModeled :: NodeModel -> ((), NodeModel)
tickModeled node@MkNodeModel{clock} = ((), node{clock = clock + 1})

-- FIXME: Replace with an executable specification generated from Agda.
fetchingModeled :: [Chain] -> [Vote] -> NodeModel -> ((), NodeModel)
fetchingModeled newChains newVotes node@MkNodeModel{self, clock, protocol, state} =
  either (error . show) id $
    runSim $ do
      stateVar <- newTVarIO state
      fetching nullTracer protocol self stateVar clock newChains newVotes
        >>= \case
          Left e -> error $ show e
          Right () -> do
            s <- readTVarIO stateVar
            pure ((), node{state = s})

-- FIXME: Replace with an executable specification generated from Agda.
blockCreationModeled :: IsSlotLeader -> Payload -> NodeModel -> (Maybe Chain, NodeModel)
blockCreationModeled isLeader payload node@MkNodeModel{self, clock, protocol, state} =
  either (error . show) id $
    runSim $ do
      stateVar <- newTVarIO state
      diffuserVar <- newTVarIO $ defaultDiffuser 0
      let party = mkSlotLeader self clock isLeader
          diffuser = diffuseChain diffuserVar
      fmap (either (error . show) id) . runExceptT $ do
        ExceptT $ blockCreation nullTracer protocol party stateVar clock payload diffuser
        s <- lift $ readTVarIO stateVar
        newChain <- assertOneChain =<< lift (popChainsAndVotes diffuserVar clock)
        pure (newChain, node{state = s})

-- FIXME: Replace with an executable specification generated from Agda.
votingModeled :: IsCommitteeMember -> NodeModel -> (Maybe Vote, NodeModel)
votingModeled isMember node@MkNodeModel{self, clock, protocol, state} =
  either (error . show) id $
    runSim $ do
      stateVar <- newTVarIO state
      diffuserVar <- newTVarIO $ defaultDiffuser 0
      let party = mkCommitteeMember self protocol clock isMember
          selectBlock' = selectBlock nullTracer
          diffuser = diffuseVote diffuserVar
      fmap (either (error . show) id) . runExceptT $ do
        ExceptT $ voting nullTracer protocol party stateVar clock selectBlock' diffuser
        s <- lift $ readTVarIO stateVar
        newVote <- assertOneVote =<< lift (popChainsAndVotes diffuserVar clock)
        pure (newVote, node{state = s})

assertOneChain :: MonadError PerasError m => ([Chain], [Vote]) -> m (Maybe Chain)
assertOneChain (newChains, newVotes) =
  case (toList newChains, toList newVotes) of
    ([], []) -> pure Nothing
    ([newChain], []) -> pure $ Just newChain
    _ -> throwError MultipleItemsDiffused

assertOneVote :: MonadError PerasError m => ([Chain], [Vote]) -> m (Maybe Vote)
assertOneVote (newChains, newVotes) =
  case (toList newChains, toList newVotes) of
    ([], []) -> pure Nothing
    ([], [newVote]) -> pure $ Just newVote
    _ -> throwError MultipleItemsDiffused

instance StateModel NodeModel where
  type Error NodeModel = PerasError

  data Action NodeModel a where
    Initialize :: Party -> SlotNumber -> PerasParams -> Action NodeModel ()
    Tick :: Action NodeModel ()
    Fetching :: [Chain] -> [Vote] -> Action NodeModel ()
    BlockCreation :: IsSlotLeader -> Payload -> Action NodeModel (Maybe Chain)
    Voting :: IsCommitteeMember -> Action NodeModel (Maybe Vote)

  initialState = MkNodeModel{self = noParty, clock = systemStart, protocol = def, state = initialPerasState}

  nextState node action _var =
    case action of
      Initialize party start params -> snd $ initializeModeled party start params node
      Tick -> snd $ tickModeled node
      Fetching newChains newVotes -> snd $ fetchingModeled newChains newVotes node
      BlockCreation isLeader payload -> snd $ blockCreationModeled isLeader payload node
      Voting isMember -> snd $ votingModeled isMember node

  precondition node@MkNodeModel{clock, protocol} =
    -- FIXME: Reconsider how constraining the preconditions should be.
    \case
      Initialize{} -> not (initialized node)
      Tick{} -> initialized node
      Fetching{} -> initialized node && not (fetched node)
      BlockCreation{} -> initialized node && not (forged node) && clock > 0
      Voting{} -> initialized node && newRound clock protocol && not (voted node)

  arbitraryAction _context node@MkNodeModel{self, clock, protocol, state = MkPerasState{..}} =
    -- FIXME: Reconsider how sophisticated these arbitrary instances should be.
    -- FIXME: Limit the size of generated instances.
    if initialized node
      then
        frequency
          [ (1, pure $ Some Tick)
          , (if fetched node then 0 else 1, fmap Some . Fetching <$> genChains <*> genVotes)
          , (if forged node || clock == 0 then 0 else 10, fmap Some . BlockCreation <$> arbitrary <*> arbitrary)
          , (if voted node then 0 else 50, Some . Voting <$> arbitrary)
          ]
      else pure . Some $ Initialize (mkParty 1 mempty mempty) (systemStart + 1) def -- FIXME: Use arbitraries.
   where
    genChains = listOf genChain
    genChain =
      do
        tip' <- elements $ toList chains
        tip <- flip drop tip' <$> arbitrary
        let minSlot =
              case tip of
                [] -> 1
                MkBlock{slotNumber} : _ -> slotNumber
        fmap (: tip) $
          MkBlock
            <$> elements [minSlot .. clock]
            <*> genPartyId
            <*> pure (hashTip tip)
            <*> genCertificate tip
            <*> arbitrary
            <*> arbitrary
            <*> arbitrary
    genVotes
      | canGenVotes = listOf genVote
      | otherwise = pure mempty
    genVote =
      do
        block <- elements =<< elements (filter (not . null) $ toList chains)
        MkVote <$> genRound <*> genPartyId <*> arbitrary <*> pure (hash block) <*> arbitrary
    canGenVotes =
      newRound clock protocol -- Voting is only allowed in the first slot of a round.
        && not (all null chains) -- There must be some block to vote for.
        && r > 0 -- No voting is allowed in the zeroth round.
    genCertificate chain =
      frequency
        [
          ( 9
          , pure Nothing
          )
        ,
          ( if null chain || null validCertRounds then 0 else 1
          , fmap Just . MkCertificate <$> elements validCertRounds <*> (hash <$> elements chain)
          )
        ]
    validCertRounds = [1 .. r] \\ (round <$> Map.keys certs)
    genPartyId = arbitrary `suchThat` (/= pid self)
    genRound = elements [1 .. r]
    r = inRound clock protocol

deriving instance Eq (Action NodeModel a)
deriving instance Show (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables = mempty

{- FIXME: There is not `MonadSTM Gen` instance, so this won't work!

-- FIXME: For now, this is tautologically hardwired so the run model is the reference model.
newtype RunMonad m a = RunMonad {runMonad :: StateT (Node.NodeState m) m a}
  deriving newtype (Functor, Applicative, Monad, MonadState (Node.NodeState m))

instance MonadSTM m => RunModel NodeModel (RunMonad m) where
  perform _node action _context =
    case action of
      Initialize party start params ->
        runExceptT $ modify' $ \impl -> impl {Node.self = party, Node.clock = start, Node.protocol = params}
      Tick ->
         runExceptT $ modify' $ \impl -> impl {Node.clock = Node.clock impl +1}
      Fetching newChains newVotes ->
        do
          Node.MkNodeState{..} <- get
          lift $ fetching nullTracer protocol self stateVar clock newChains newVotes
      BlockCreation isLeader payload ->
        runExceptT $ do
          Node.MkNodeState{..} <- get
          let party = mkSlotLeader self clock isLeader
          ExceptT . lift $ do
            atomically $ writeTVar diffuserVar $ defaultDiffuser 0
            blockCreation nullTracer protocol party stateVar clock payload $ diffuseChain diffuserVar
          (lift . lift $ popChainsAndVotes diffuserVar clock)
              >>= assertOneChain
      Voting isMember ->
        runExceptT $ do
          Node.MkNodeState{..} <- get
          let party = mkCommitteeMember self protocol clock isMember
              selectBlock' = selectBlock nullTracer
          ExceptT . lift $ do
            atomically $ writeTVar diffuserVar $ defaultDiffuser 0
            voting nullTracer protocol party stateVar (inRound clock protocol) selectBlock' $ diffuseVote diffuserVar
          (lift . lift $ popChainsAndVotes diffuserVar clock)
              >>= assertOneVote

  postcondition (prior, _) action _env =
    case action of
      Initialize party start params -> check $ initializeModeled party start params
      Tick -> check tickModeled
      Fetching newChains newVotes -> check $ fetchingModeled newChains newVotes
      BlockCreation isLeader payload -> check $ blockCreationModeled isLeader payload
      Voting isMember -> check $ votingModeled isMember
    where
      check :: (Monad m, Eq a) => (NodeModel -> (a, NodeModel)) -> a -> m Bool
      check action' actual =
        pure $ fst (action' prior) == actual
-}

-- FIXME: For now, this is tautologically hardwired so the run model is the reference model.
newtype RunMonad m a = RunMonad {runMonad :: StateT NodeModel m a}
  deriving newtype (Functor, Applicative, Monad, MonadState NodeModel)

instance Monad m => RunModel NodeModel (RunMonad m) where
  perform _node action _context =
    case action of
      Initialize party start params ->
        runExceptT $
          modify' $
            \node -> node{self = party, clock = start, protocol = params}
      Tick ->
        runExceptT $
          modify' $
            \node -> node{clock = clock node + 1}
      Fetching newChains newVotes ->
        runExceptT $ do
          MkNodeModel{..} <- get
          state' <-
            ExceptT . either (error . show) pure $
              runSim $ do
                stateVar <- newTVarIO state
                runExceptT $ do
                  ExceptT $ fetching nullTracer protocol self stateVar clock newChains newVotes
                  lift $ readTVarIO stateVar
          modify' $ \node -> node{state = state'}
      BlockCreation isLeader payload ->
        runExceptT $ do
          MkNodeModel{..} <- get
          (newChain, state') <-
            ExceptT . either (error . show) pure $
              runSim $ do
                stateVar <- newTVarIO state
                diffuserVar <- newTVarIO $ defaultDiffuser 0
                let party = mkSlotLeader self clock isLeader
                    diffuser = diffuseChain diffuserVar
                runExceptT $ do
                  ExceptT $ blockCreation nullTracer protocol party stateVar clock payload diffuser
                  (,)
                    <$> (assertOneChain =<< lift (popChainsAndVotes diffuserVar clock))
                    <*> lift (readTVarIO stateVar)
          modify' $ \node -> node{state = state'}
          pure newChain
      Voting isMember ->
        runExceptT $ do
          MkNodeModel{..} <- get
          (newVote, state') <-
            ExceptT . either (error . show) pure $
              runSim $ do
                stateVar <- newTVarIO state
                diffuserVar <- newTVarIO $ defaultDiffuser 0
                let party = mkCommitteeMember self protocol clock isMember
                    selectBlock' = selectBlock nullTracer
                    diffuser = diffuseVote diffuserVar
                runExceptT $ do
                  ExceptT $ voting nullTracer protocol party stateVar clock selectBlock' diffuser
                  (,)
                    <$> (assertOneVote =<< lift (popChainsAndVotes diffuserVar clock))
                    <*> lift (readTVarIO stateVar)
          modify' $ \node -> node{state = state'}
          pure newVote

  postcondition (prior, _) action _env =
    case action of
      Initialize party start params -> check $ initializeModeled party start params
      Tick -> check tickModeled
      Fetching newChains newVotes -> check $ fetchingModeled newChains newVotes
      BlockCreation isLeader payload -> check $ blockCreationModeled isLeader payload
      Voting isMember -> check $ votingModeled isMember
   where
    check :: (Monad m', Eq a) => (NodeModel -> (a, NodeModel)) -> a -> m' Bool
    check action' actual =
      pure $ fst (action' prior) == actual

instance MonadTrans RunMonad where
  lift = RunMonad . lift

type instance Realized (RunMonad m) () = ()
type instance Realized (RunMonad m) (Maybe Chain) = (Maybe Chain)
type instance Realized (RunMonad m) (Maybe Vote) = (Maybe Vote)
