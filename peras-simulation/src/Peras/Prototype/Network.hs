{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- | Simulate the network environment for a single node.
module Peras.Prototype.Network where

import Control.Concurrent.Class.MonadSTM (MonadSTM (TVar, modifyTVar'), atomically, newTVarIO, readTVarIO, writeTVar)
import Control.Monad (forM, when)
import Control.Monad.Class.MonadTimer (MonadDelay, threadDelay)
import Control.Monad.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.State (StateT, execStateT, gets, modify', runStateT)
import Control.Monad.Trans (lift)
import Control.Tracer (Tracer, traceWith)
import qualified Data.Aeson as A
import Data.Default (Default (..))
import Data.Foldable (toList)
import Data.Functor (void)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Peras.Block (Party (MkParty, pid), PartyId)
import Peras.Numbering (RoundNumber, SlotNumber)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Diffusion (Diffuser, defaultDiffuser, mergeDiffusers, popChainsAndVotes)
import Peras.Prototype.Node (NodeState (MkNodeState, clock, diffuserVar, stateVar), initialNodeState, tick, tickNode)
import Peras.Prototype.Trace (PerasLog (..))
import Peras.Prototype.Types (Payload, PerasParams (..), PerasResult, PerasState, inRound, initialPerasState, systemStart)

-- | Simulate a `Network` as the interaction of an `Environment` and a single `Node`.
-- The given @scenario@ function is used to generate the incoming chains and votes for each slot.
simulateNetwork :: forall m. (MonadSTM m, MonadDelay m) => Tracer m PerasLog -> (SlotNumber -> m Diffuser) -> m PerasState
simulateNetwork tracer scenario = do
  let voteEvery10Rounds = mkParty 42 [] [10]
  initial <- initialNodeState tracer voteEvery10Rounds 0 def
  execStateT loop initial >>= \MkNodeState{stateVar} -> readTVarIO stateVar
 where
  loop = do
    -- 1. feed the diffuser with incoming chains and votes
    slot <- gets clock
    diffuser <- gets diffuserVar
    updateIncomingFromScenario diffuser slot
    -- 2. Tick the node triggering fetching, block creation, and voting processes
    void $ tick tracer []
    -- 3. drain diffuser from possible votes and blocks emitted by the node.
    lift $ atomically $ writeTVar diffuser $ defaultDiffuser 0
    loop

  updateIncomingFromScenario diffuser slot = lift $ do
    diffuser' <- scenario slot
    atomically $ modifyTVar' diffuser $ \pending -> mergeDiffusers pending diffuser'

data Network m = MkNetwork
  { netClock :: SlotNumber
  , protocol :: PerasParams
  , stateVars :: Map Party (TVar m PerasState)
  , netDiffuserVar :: TVar m Diffuser
  }

initialNetwork :: MonadSTM m => Tracer m PerasLog -> Set Party -> SlotNumber -> PerasParams -> m (Network m)
initialNetwork tracer parties netClock protocol =
  do
    traceWith tracer $ Protocol protocol
    stateVars <- Map.fromList <$> mapM ((<$> newTVarIO initialPerasState) . (,)) (toList parties)
    netDiffuserVar <- newTVarIO $ defaultDiffuser (perasΔ protocol)
    pure MkNetwork{..}

-- | Run a `Network` comprised of multiple interacting nodes, with some `Payload`.
runNetwork :: forall m. MonadSTM m => Tracer m PerasLog -> Payload -> StateT (Network m) m (PerasResult ())
runNetwork tracer payload = do
  params <- gets protocol
  states <- gets stateVars
  diffuser <- gets netDiffuserVar
  -- Increment clock.
  s <- gets $ (1 +) . netClock
  modify' $ \net -> net{netClock = s}
  let r = inRound s params
  lift $ traceWith tracer $ Tick s r
  -- Retrieve chains and votes to be diffused.
  (newChains, newVotes) <- lift $ popChainsAndVotes diffuser s
  -- Operate nodes.
  fmap sequence_ . forM (Map.toList states) $ \(party, state) ->
    lift $ tickNode tracer diffuser params party state s r payload newChains newVotes

data PartyConfig = MkPartyConfig
  { leadershipSlots :: Set SlotNumber
  , membershipRounds :: Set RoundNumber
  , perasState :: PerasState
  }
  deriving (Eq, Generic, Show)

instance A.FromJSON PartyConfig
instance A.ToJSON PartyConfig

instance Default PartyConfig where
  def = MkPartyConfig def def def

data SimConfig = MkSimConfig
  { start :: SlotNumber
  , finish :: SlotNumber
  , params :: PerasParams
  , parties :: Map PartyId PartyConfig
  , payloads :: Map SlotNumber Payload
  , diffuser :: Diffuser
  }
  deriving (Eq, Generic, Show)

instance A.FromJSON SimConfig
instance A.ToJSON SimConfig

instance Default SimConfig where
  def =
    MkSimConfig
      { start = systemStart
      , finish = systemStart + 1
      , params = def
      , parties = def
      , payloads = def
      , diffuser = def
      }

data SimAction = SimRun | SimStop | SimStep | SimPause
  deriving (Eq, Generic, Show)

instance A.FromJSON SimAction
instance A.ToJSON SimAction

data SimControl = MkSimControl
  { delay :: Int
  , action :: SimAction
  }
  deriving (Eq, Generic, Show)

instance A.FromJSON SimControl
instance A.ToJSON SimControl

instance Default SimControl where
  def = MkSimControl 100_000 SimRun

simulate :: forall m. (MonadDelay m, MonadSTM m) => Tracer m PerasLog -> TVar m SimControl -> SimConfig -> m (PerasResult SimConfig)
simulate tracer controlVar initial =
  do
    let mkState partyId MkPartyConfig{..} =
          (mkParty partyId (toList leadershipSlots) (toList membershipRounds),)
            <$> newTVarIO perasState
    net <-
      MkNetwork (start initial) (params initial)
        <$> (Map.fromList <$> mapM (uncurry mkState) (Map.toList $ parties initial))
        <*> newTVarIO (diffuser initial)
    traceWith tracer . Protocol $ params initial
    let go count =
          do
            MkSimControl{delay, action} <- lift . lift $ readTVarIO controlVar
            lift . lift $ threadDelay delay
            case if count <= 0 then SimStop else action of
              SimStop -> pure ()
              SimPause -> go count
              _ -> do
                payload <- gets $ fromMaybe mempty . (`Map.lookup` payloads initial) . netClock
                ExceptT $ runNetwork tracer payload
                when (action == SimStep)
                  . lift
                  . lift
                  . atomically
                  $ modifyTVar' controlVar (\c -> c{action = SimPause})
                go $ count - 1
    (result, net') <- flip runStateT net . runExceptT . go $ finish initial - start initial
    case result of
      Left e -> pure $ Left e
      Right _ -> do
        diffuser <- readTVarIO $ netDiffuserVar net'
        let s = netClock net'
            r = inRound s $ protocol net'
            mkPartyConfig :: Party -> TVar m PerasState -> m (PartyId, PartyConfig)
            mkPartyConfig MkParty{pid} stateVar =
              do
                perasState <- readTVarIO stateVar
                let partyConfig = parties initial Map.! pid :: PartyConfig
                pure
                  ( pid
                  , MkPartyConfig
                      { perasState
                      , leadershipSlots = Set.filter (<= s) $ leadershipSlots partyConfig
                      , membershipRounds = Set.filter (<= r) $ membershipRounds partyConfig
                      }
                  )
        parties' <- Map.fromList <$> mapM (uncurry mkPartyConfig) (Map.toList $ stateVars net')
        pure . Right $
          MkSimConfig
            { start = netClock net'
            , finish = finish initial
            , params = protocol net'
            , parties = parties'
            , payloads = Map.filterWithKey (const . (>= netClock net')) $ payloads initial
            , diffuser
            }
