{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Abstract.Protocol.Node.Model (

) where

import Control.Concurrent.Class.MonadSTM
import Control.Monad.IOSim
import Control.Monad.State (
  MonadState (get, put),
  MonadTrans,
  State,
  StateT (StateT),
  evalState,
  execState,
  lift,
 )
import Control.Tracer (nullTracer)
import Data.Set (Set)
import Peras.Abstract.Protocol.BlockCreation (blockCreation)
import Peras.Abstract.Protocol.Fetching (fetching)
import Peras.Abstract.Protocol.Preagreement (preagreement)
import Peras.Abstract.Protocol.Trace (PerasLog, perasTracer)
import Peras.Abstract.Protocol.Types
import Peras.Abstract.Protocol.Voting (voting)
import Peras.Block
import Peras.Chain
import Peras.Numbering
import Test.QuickCheck (arbitrary, elements, frequency, listOf, suchThat)
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (Any (Some), HasVariables (..), Realized, RunModel (perform, postcondition), StateModel (..))

data NodeModel = MkNodeModel
  { self :: Party
  , clock :: SlotNumber
  , protocol :: PerasParams
  , state :: PerasState
  }
  deriving (Eq, Show)

instance HasVariables NodeModel where
  getAllVariables = mempty

instance DynLogicModel NodeModel

instance StateModel NodeModel where
  data Action NodeModel a where
    Initialize :: Party -> SlotNumber -> PerasParams -> Action NodeModel ()
    Tick :: Action NodeModel ()
    Fetching :: Set Chain -> Set Vote -> Action NodeModel [PerasLog]
    BlockCreation :: Payload -> Action NodeModel [PerasLog]
    Voting :: Action NodeModel [PerasLog]

  initialState = MkNodeModel{self = error "Must specify a party", clock = systemStart, protocol = defaultParams, state = initialPerasState}

  nextState model@MkNodeModel{self, clock, protocol, state} action _var =
    either (error . show) id $
      runSim $ do
        stateVar <- newTVarIO state
        case action of
          -- FIXME: Reducing repetition is tricky because of how `IOSim` is definited with existential types.
          Initialize party start params -> pure model{self = party, clock = start, protocol = params, state = initialPerasState}
          Tick -> pure model{clock = clock + 1}
          Fetching newChains newVotes ->
            fetching nullTracer protocol self stateVar clock newChains newVotes
              >>= either (error . (show :: PerasError -> String)) (\() -> do s <- readTVarIO stateVar; pure model{state = s})
          BlockCreation payload ->
            blockCreation nullTracer protocol self stateVar clock payload diffuser
              >>= either (error . (show :: PerasError -> String)) (\() -> do s <- readTVarIO stateVar; pure model{state = s})
           where
            diffuser = const . const . pure $ pure ()
          Voting ->
            voting nullTracer protocol self stateVar (inRound clock protocol) (preagreement nullTracer) diffuser
              >>= either (error . (show :: PerasError -> String)) (\() -> do s <- readTVarIO stateVar; pure model{state = s})
           where
            diffuser = const . const . pure $ pure ()

{-
  precondition node =
    \case
      Initialize{} -> True
      Fetching{} -> True
      BlockCreation{} -> True
      Voting{} -> (node ^. currentSlot) `mod` paramU (node ^. protocol) == 0

  arbitraryAction _context node =
    -- FIXME: Reconsider how sophisticated these arbitrary instances should be.
    -- FIXME: Limit the size of generated instances.
    if uninitialized
      then fmap Some . Initialize <$> arbitrary <*> arbitrary
      else
        frequency
          [ (5, fmap Some . Fetching <$> listOf genChain <*> genVotes)
          , (1, Some . BlockCreation <$> arbitrary)
          , (if newRound then 50 else 0, Some . Voting <$> arbitrary)
          ]
   where
    uninitialized = (node ^. creatorId) == MakeVerificationKey mempty
    newRound = (node ^. currentSlot) > 0 && (node ^. currentSlot) `mod` paramU (node ^. protocol) == 0
    someBlocks = node ^. chains /= [[]]
    genParty = arbitrary `suchThat` (/= (node ^. creatorId))
    genChain =
      do
        tip' <- elements $ node ^. chains
        tip <- flip drop tip' <$> arbitrary
        block <- signBlock (node ^. currentSlot) <$> genParty <*> pure (tipHash tip) <*> pure Nothing <*> arbitrary
        pure $ block : tip
    genVotes
      | someBlocks = listOf genVote
      | otherwise = pure mempty
    genVote =
      do
        block <- elements =<< elements (node ^. chains)
        signVote (node ^. currentRound) <$> genParty <*> arbitrary <*> pure block
-}
deriving instance Eq (Action NodeModel a)
deriving instance Show (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables = mempty

{-
newtype RunMonad n m a = RunMonad {runMonad :: StateT n m a}
  deriving newtype (Functor, Applicative, Monad, MonadState n)

instance MonadTrans (RunMonad n) where
  lift = RunMonad . lift

type instance Realized (RunMonad n m) [Message] = [Message]

instance (Monad m, API.PerasNode n m) => RunModel NodeState (RunMonad n m) where
  perform _state (Initialize params party) _context = apply $ API.initialize params party
  perform _state (Fetching chains' votes') _context = apply $ API.fetching chains' votes'
  perform _state (BlockCreation txs) _context = apply $ API.blockCreation txs
  perform _state (Voting weight) _context = apply $ API.voting weight

  postcondition (prior, _) (Initialize params party) _env actual = check prior actual $ Specification.initialize params party
  postcondition (prior, _) (Fetching chains' votes') _env actual = check prior actual $ Specification.fetching chains' votes'
  postcondition (prior, _) (BlockCreation txs) _env actual = check prior actual $ Specification.blockCreation txs
  postcondition (prior, _) (Voting weight) _env actual = check prior actual $ Specification.voting weight

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
-}
