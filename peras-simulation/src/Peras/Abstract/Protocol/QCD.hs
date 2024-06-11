{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
module Peras.Abstract.Protocol.QCD where

import Prelude hiding (round)
import Control.Monad
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Ord
import Data.List
import Control.Tracer
import Control.Concurrent.Class.MonadSTM
import Control.Monad.State hiding (state)
import Data.Maybe
import Data.Foldable ()
import Data.Default
import Peras.Chain
import Peras.Block
import Peras.Crypto
import Peras.Numbering
import Peras.Arbitraries ()
import Peras.Abstract.Protocol.Types
import Peras.Abstract.Protocol.Fetching
import Peras.Abstract.Protocol.Preagreement
import Peras.Abstract.Protocol.Crypto
import Peras.Abstract.Protocol.Diffusion
import Peras.Abstract.Protocol.Voting
import Test.QuickCheck
import Test.QuickCheck.StateModel
import Test.QuickCheck.Extras
import Test.QuickCheck.Monadic
import Control.Concurrent.STM.TVar qualified as IO

data NodeModel = MkNodeModel
  { modelSUT  :: Party
  , clock     :: SlotNumber
  , protocol  :: PerasParams
  , allChains :: [Chain]
  }
  deriving (Eq, Show)

instance HasVariables NodeModel where
  getAllVariables _ = mempty

instance Show (Action NodeModel a) where
  show (Step a) = show a
deriving instance Eq (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables _ = mempty

data EnvAction = Tick | NewChain Chain | NewVote Vote
  deriving (Show, Eq, Generic)

preferredChain :: [Chain] -> Chain
preferredChain []      = []
preferredChain (c : _) = c

lastSeenCert :: [Chain] -> Certificate
lastSeenCert chains = maximumBy (comparing round) $ [ cert | c <- chains, MkBlock{certificate = Just cert} <- c ]
                                                 ++ [genesisCert]

votesInState :: NodeModel -> Set Vote
votesInState MkNodeModel{protocol = protocol@MkPerasParams{..}, ..}
  | Just vote <- getVote = Set.singleton vote
  | otherwise = mempty
  where
    getVote = do
      let r = inRound clock protocol
          pref  = preferredChain allChains
          cert' = lastSeenCert allChains
          party = mkCommitteeMember modelSUT protocol clock True
      guard $ mod (getSlotNumber clock) perasU == perasT
      guard $ round cert' + 1 == r  -- VR-1A
      block <- listToMaybe $ dropWhile (not . oldEnough) pref
      guard $ extends block cert' allChains -- VR-1B
      Right proof <- createMembershipProof r (Set.singleton party)
      Right vote  <- createSignedVote party r (hash block) proof 1
      pure vote
    oldEnough MkBlock{..} = getSlotNumber slotNumber + perasL <= getSlotNumber clock - perasT

transition :: NodeModel -> EnvAction -> Maybe (Set Vote, NodeModel)
transition s a = case a of
  Tick -> Just (votesInState s', s')
    where s' = s { clock = clock s + 1 }
  NewChain c -> Just (mempty, s { allChains = c : allChains s })
  _ -> Just (mempty, s)

instance StateModel NodeModel where
  data Action NodeModel a where
    Step :: EnvAction -> Action NodeModel (Set Vote)

  initialState = MkNodeModel{ modelSUT = mkParty 1 mempty [0..10_000] -- Never the slot leader, always a committee member
                            , clock = systemStart + 1
                            , protocol = def { perasU = 5
                                             , perasR = 2
                                             , perasK = 4
                                             , perasL = 1
                                             , perasT = 4
                                             , perasΔ = 1
                                             }
                            , allChains = [genesisChain]
                            }

  arbitraryAction _ MkNodeModel{modelSUT, clock, allChains} = Some . Step <$>
      frequency [ (1, pure Tick)
                , (1, NewChain <$> genChain)
                , (1, NewVote  <$> genVote)
                ]
    where
      genChain =
        do
          tip' <- elements allChains
          n <- choose (0, length tip' - 1)
          let tip = drop n tip'
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

      genCertificate _ = pure Nothing -- TODO
      genVote = arbitrary
      genPartyId = arbitrary `suchThat` (/= pid modelSUT)

  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ (Step (NewChain (_:chain))) = map (Some . Step) [Tick, NewChain chain]
  shrinkAction _ _ (Step _) = [Some (Step Tick)]

  precondition s (Step a) = isJust (transition s a)

  nextState s (Step a) _ = snd . fromJust $ transition s a

data RunState m =
  RunState { stateVar        :: TVar m PerasState
           , diffuserVar     :: TVar m Diffuser
           , unfetchedChains :: Set Chain
           , unfetchedVotes  :: Set Vote
           }

type Runtime m = StateT (RunState m) m

instance (Realized m (Set Vote) ~ Set Vote, MonadSTM m) => RunModel NodeModel (Runtime m) where
  perform MkNodeModel{..} (Step a) _ = case a of
    Tick -> do
      RunState{..} <- get
      modify $ \ rs -> rs { unfetchedChains = mempty, unfetchedVotes = mempty }
      lift $ do
        let clock' = clock + 1
        -- TODO: also invoke blockCreation
        _ <- fetching nullTracer protocol modelSUT stateVar clock' unfetchedChains unfetchedVotes
        let party = mkCommitteeMember modelSUT protocol clock' True
            preagreement' = preagreement nullTracer
            diffuser = diffuseVote diffuserVar
        _ <- voting nullTracer protocol party stateVar (inRound clock' protocol) preagreement' diffuser
        snd <$> popChainsAndVotes diffuserVar clock'
    NewChain c -> do
      modify $ \ rs -> rs { unfetchedChains = Set.insert c (unfetchedChains rs) }
      pure mempty
    NewVote v -> do
      modify $ \ rs -> rs { unfetchedVotes = Set.insert v (unfetchedVotes rs) }
      pure mempty

  postcondition (s, s') (Step a) _ r = do
    let expected = fromJust $ fmap fst (transition s a)
    let ok = r == expected
    monitorPost . counterexample $ "  action $ " ++ show a
    when (a == Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $ "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (null r) $ do
      monitorPost . counterexample $ "  -- got: " ++ show (Set.toList r)
    unless ok $ do
      monitorPost . counterexample $ "  -- expected: " ++ show (Set.toList expected)
    pure ok

prop_node :: Blind (Actions NodeModel) -> Property
prop_node (Blind as) = monadicIO $ do
  stateVar <- lift $ IO.newTVarIO initialPerasState
  diffuserVar <- lift $ IO.newTVarIO def
  let unfetchedChains = mempty
      unfetchedVotes = mempty
  monitor $ counterexample "do"
  _ <- runPropertyStateT (runActions @_ @(Runtime IO) as) RunState{..}
  pure True
