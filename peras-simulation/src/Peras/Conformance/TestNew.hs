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
  checkVotingRules,
  initialModelState,
  otherId,
  pref,
  sutIsSlotLeader,
  testParams,
  transition,
  votingBlockHash,
 )
import Peras.Conformance.Model qualified as Model
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

newtype NetworkModel = NetworkModel {getNodeModel :: NodeModel}
  deriving (Show)

instance HasVariables NetworkModel where
  getAllVariables _ = mempty

instance DynLogicModel NetworkModel

instance Show (Action NetworkModel a) where
  show (Step a) = show a
deriving instance Eq (Action NetworkModel a)

instance HasVariables (Action NetworkModel a) where
  getAllVariables _ = mempty

instance Pretty NetworkModel where
  pPrint (NetworkModel (NodeModel{..})) =
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

-- Slot leader every third slot, always a committee member
-- FIXME: randomize slot leader slots
modelSUT :: Party
modelSUT = mkParty 1 (filter sutIsSlotLeader [0 .. 10_000]) [0 .. 10_000]

gen :: GenConstraints
gen =
  if True
    then strictGenConstraints
    else votingGenConstraints

instance StateModel NetworkModel where
  data Action NetworkModel a where
    Step :: EnvAction -> Action NetworkModel ([Chain], [Vote])

  initialState = NetworkModel initialModelState

  arbitraryAction _ s@(NetworkModel (NodeModel{clock, allChains, allVotes, protocol})) =
    pure . Some $ Step Tick

  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ (Step (NewChain (_ : chain))) = map (Some . Step) [Tick, NewChain chain]
  shrinkAction _ _ (Step _) = [Some (Step Tick)]

  precondition (NetworkModel s) (Step a) = isJust $ transition s a

  nextState (NetworkModel s) (Step a) _ = NetworkModel $ maybe s snd $ transition s a

monitorVoting :: Monad m => NodeModel -> PostconditionM m ()
monitorVoting s@NodeModel{clock, protocol} =
  when (newRound (clock + 1) protocol) $
    do
      monitorPost $ tabulate "Voting rules" [show $ checkVotingRules s']
      monitorPost $ tabulate "VR-1A/1B/2A/2B" [init . tail $ show (Model.vr1A s', Model.vr1B s', Model.vr2A s', Model.vr2B s')]
      monitorPost $ tabulate "Expected votes" [show $ maybe 0 (length . snd . fst) $ transition s Tick]
 where
  s' = s{clock = clock + 1}
