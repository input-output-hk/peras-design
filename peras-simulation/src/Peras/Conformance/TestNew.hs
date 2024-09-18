{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Conformance.TestNew where

import Control.Monad (when)
import Data.Maybe (Maybe (..), fromJust, isJust)
import Data.Set (Set)
import Debug.Trace (traceShow)
import Peras.Arbitraries ()
import Peras.Block (Block (..), Certificate (..), Party (pid), tipHash)
import Peras.Chain (Chain, Vote (..))
import Peras.Conformance.Generators
import Peras.Conformance.Model (
  EnvAction (..),
  NodeModel (..),
  SutIsSlotLeader,
  SutIsVoter,
  checkVotingRules,
  initialModelState,
  otherId,
  pref,
  testParams,
  transition,
  votingBlockHash,
 )
import Peras.Conformance.Model qualified as Model
import Peras.Conformance.Params
import Peras.Crypto (Hashable (hash))
import Peras.Foreign qualified as Foreign
import Peras.Numbering (
  RoundNumber (getRoundNumber),
  SlotNumber (getSlotNumber),
  slotToRound,
 )
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Trace qualified as Trace
import Peras.Prototype.Types (hashTip, inRound, newRound)
import Test.QuickCheck (
  Arbitrary (arbitrary),
  choose,
  elements,
  frequency,
  suchThat,
  tabulate,
 )
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.Gen
import Test.QuickCheck.StateModel (
  Any (Some),
  HasVariables (..),
  PostconditionM,
  StateModel (
    Action,
    arbitraryAction,
    initialState,
    nextState,
    precondition,
    shrinkAction
  ),
  monitorPost,
 )
import Text.PrettyPrint (braces, hang, text, vcat, (<+>))
import Text.PrettyPrint.HughesPJClass (
  Pretty (pPrint, pPrintPrec),
  maybeParens,
  prettyNormal,
 )
import Prelude hiding (round)

data NetworkModel = NetworkModel
  { nodeModel :: NodeModel
  , leadershipSlots :: [SlotNumber]
  , voterRounds :: [RoundNumber]
  , gen :: GenConstraints
  , initialized :: Bool
  }
  deriving (Show)

instance HasVariables NetworkModel where
  getAllVariables _ = mempty

instance DynLogicModel NetworkModel

instance Show (Action NetworkModel a) where
  show Initial{} = "Initial"
  show (Step a) = show a
deriving instance Eq (Action NetworkModel a)

instance HasVariables (Action NetworkModel a) where
  getAllVariables _ = mempty

instance Pretty NetworkModel where
  pPrint (NetworkModel{nodeModel = NodeModel{..}}) =
    hang "NetworkModel" 2 $
      braces $
        vcat
          [ hang "clock =" 2 $ pPrint (getSlotNumber clock)
          , hang "allChains =" 2 $ vcat (map pPrint allChains)
          , hang "allVotes =" 2 $ pPrint allVotes
          , hang "allSeenCerts =" 2 $ vcat (map pPrint allSeenCerts)
          ]

instance Pretty EnvAction where
  pPrint Tick = "Tick"
  pPrint (NewChain chain) =
    "NewChain" <+> pPrint chain
  pPrint (NewVote vote) = "NewVote" <+> pPrintPrec prettyNormal 10 vote
  pPrint (BadVote vote) = "BadVote" <+> pPrintPrec prettyNormal 10 vote

instance Pretty Block where
  pPrint b@MkBlock{..} =
    "Block"
      <+> braces
        ( vcat
            [ "hash            =" <+> text (show $ hash b)
            , "slot            =" <+> pPrint (getSlotNumber slotNumber)
            , "creator         =" <+> pPrint creatorId
            , "parent          =" <+> text (show parentBlock)
            , "leadershipProof =" <+> text (show leadershipProof)
            , "signature       =" <+> text (show signature)
            , "cert            =" <+> pPrint certificate
            , "bodyHash        =" <+> text (show bodyHash)
            ]
        )

instance Pretty Certificate where
  pPrintPrec _ d MkCertificate{..} =
    maybeParens (d > 0) $ "Cert" <+> pPrint (getRoundNumber round) <+> text (show blockRef)

instance Pretty Vote where
  pPrintPrec _ d MkVote{..} =
    maybeParens (d > 0) $
      "Vote"
        <+> braces
          ( vcat
              [ "round     =" <+> pPrint (getRoundNumber votingRound)
              , "creator   =" <+> pPrint creatorId
              , "blockHash =" <+> text (show blockHash)
              , "proofM    =" <+> text (show proofM)
              , "signature =" <+> text (show signature)
              ]
          )

instance Pretty Trace.PerasLog where
  pPrint = \case
    Trace.Protocol{} -> "Protocol"
    Trace.Tick{} -> "Tick"
    Trace.NewChainAndVotes{newChains, newVotes} ->
      hang "NewChainAndVotes" 2 $
        vcat $
          [hang "Chains:" 2 $ vcat (map pPrint newChains) | not $ null newChains]
            ++ [hang "Votes:" 2 $ vcat (map pPrint newVotes) | not $ null newVotes]
    Trace.NewChainPref{newChainPref} -> hang "NewChainPref:" 2 $ pPrint newChainPref
    Trace.NewCertificatesReceived{newCertificates} ->
      hang "NewCerts:" 2 $
        vcat [pPrint (getSlotNumber slot) <+> ":" <+> pPrint cert | (cert, slot) <- newCertificates]
    Trace.NewCertificatesFromQuorum{newQuorums} ->
      hang "NewQuorums:" 2 $ pPrint newQuorums
    Trace.NewCertPrime{newCertPrime} -> hang "NewCertPrime:" 2 (pPrint newCertPrime)
    Trace.NewCertStar{newCertStar} -> hang "NewCertStar:" 2 (pPrint newCertStar)
    Trace.CastVote{vote} -> hang "CastVote:" 2 (pPrint vote)
    Trace.SelectedBlock{block} -> hang "SelectedBlock:" 2 $ pPrint block
    Trace.NoBlockSelected{} -> "NoBlockSelected"
    Trace.ForgingLogic{} -> "ForgingLogic"
    Trace.VotingLogic{vr1a, vr1b, vr2a, vr2b} ->
      hang "VotingLogic:" 2 $
        vcat
          [ "VR-1A =" <+> pPrint vr1a
          , "VR-1B =" <+> pPrint vr1b
          , "VR-2A =" <+> pPrint vr2a
          , "VR-2B =" <+> pPrint vr2b
          ]
    Trace.DiffuseChain{chain} ->
      hang "DiffuseChain:" 2 $ pPrint chain
    Trace.DiffuseVote{vote} ->
      hang "DiffuseVote" 2 $ pPrint vote

sortition :: NetworkModel -> (SutIsSlotLeader, SutIsVoter)
sortition NetworkModel{leadershipSlots, voterRounds} = (flip elem leadershipSlots, flip elem voterRounds)

modelSUT :: NetworkModel -> Party
modelSUT NetworkModel{leadershipSlots, voterRounds} = mkParty 1 leadershipSlots voterRounds

instance StateModel NetworkModel where
  data Action NetworkModel a where
    Initial :: PerasParams -> [SlotNumber] -> [RoundNumber] -> Action NetworkModel ()
    Step :: EnvAction -> Action NetworkModel ([Chain], [Vote])

  initialState =
    NetworkModel
      { nodeModel = initialModelState
      , leadershipSlots = filter ((== 1) . (`mod` 3)) [0 .. 10_000]
      , voterRounds = [0 .. 10_000]
      , gen = strictGenConstraints
      , initialized = useTestParams strictGenConstraints
      }

  arbitraryAction _ s@NetworkModel{nodeModel = NodeModel{clock, allChains, allVotes, protocol}, gen, initialized} =
    if initialized
      then pure . Some $ Step Tick
      else fmap Some $
        do
          params <- genProtocol gen
          let slotLimit = 10_000
              roundLimit = fromIntegral $ fromIntegral slotLimit `div` perasU params
          Initial params
            <$> genSlotLeadership 0.30 slotLimit
            <*> genCommitteeMembership 0.95 roundLimit

  shrinkAction _ _ Initial{} = []
  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ (Step (NewChain (_ : chain))) = Some . Step <$> [Tick, NewChain chain]
  shrinkAction _ _ Step{} = [Some (Step Tick)]

  precondition NetworkModel{initialized} Initial{} = not initialized
  precondition net@NetworkModel{nodeModel = s} (Step a) = isJust $ transition (sortition net) s a

  nextState net@NetworkModel{nodeModel = s} (Initial params slots rounds) _ =
    net{nodeModel = s{protocol = params}, leadershipSlots = slots, voterRounds = rounds, initialized = True}
  nextState net@NetworkModel{nodeModel = s} (Step a) _ =
    net{nodeModel = maybe s snd $ transition (sortition net) s a}

monitorVoting :: Monad m => NetworkModel -> PostconditionM m ()
monitorVoting net@NetworkModel{nodeModel = s@NodeModel{clock, protocol}} =
  when (newRound (clock + 1) protocol) $
    do
      monitorPost $ tabulate "Voting rules" [show $ checkVotingRules s']
      monitorPost $ tabulate "VR-1A/1B/2A/2B" [init . tail $ show (Model.vr1A s', Model.vr1B s', Model.vr2A s', Model.vr2B s')]
      monitorPost $ tabulate "Committee member" [show $ snd (sortition net) r | let r = inRound (clock + 1) protocol]
      monitorPost $ tabulate "Does vote" [show $ maybe 0 (length . snd . fst) $ transition (sortition net) s Tick]
 where
  s' = s{clock = clock + 1}
