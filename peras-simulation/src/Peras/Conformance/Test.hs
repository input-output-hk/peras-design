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

module Peras.Conformance.Test where

import Data.Maybe (Maybe (..), fromJust, isJust)
import Data.Set (Set)
import Peras.Arbitraries ()
import Peras.Block (Block (..), Certificate (..), Party (pid))
import Peras.Chain (Vote (..))
import Peras.Conformance.Model (
  EnvAction (..),
  NodeModel (..),
  initialModelState,
  transition,
 )
import Peras.Crypto (Hashable (hash))
import Peras.Numbering (
  RoundNumber (getRoundNumber),
  SlotNumber (getSlotNumber),
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
 )
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (
  Any (Some),
  HasVariables (..),
  StateModel (
    Action,
    arbitraryAction,
    initialState,
    nextState,
    precondition,
    shrinkAction
  ),
 )
import Text.PrettyPrint (braces, hang, text, vcat, (<+>))
import Text.PrettyPrint.HughesPJClass (
  Pretty (pPrint, pPrintPrec),
  maybeParens,
  prettyNormal,
 )
import Prelude hiding (round)

instance HasVariables NodeModel where
  getAllVariables _ = mempty

instance DynLogicModel NodeModel

instance Show (Action NodeModel a) where
  show (Step a) = show a
deriving instance Eq (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables _ = mempty

instance Pretty NodeModel where
  pPrint NodeModel{..} =
    hang "NodeModel" 2 $
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
  pPrint MkBlock{..} =
    "Block"
      <+> braces
        ( vcat
            [ "hash    =" <+> text (show signature)
            , "slot    =" <+> pPrint (getSlotNumber slotNumber)
            , "creator =" <+> pPrint creatorId
            , "parent  =" <+> text (show parentBlock)
            , "cert    =" <+> pPrint certificate
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

modelSUT :: Party
modelSUT = mkParty 1 mempty [0 .. 10_000] -- Never the slot leader, always a committee member

instance StateModel NodeModel where
  data Action NodeModel a where
    Step :: EnvAction -> Action NodeModel [Vote]

  initialState = initialModelState

  arbitraryAction _ NodeModel{clock, allChains, allVotes, protocol} =
    fmap (Some . Step) $
      frequency $
        [(1, pure Tick)]
          ++ [(1, NewChain <$> genChain)]
          ++ [(8, NewVote <$> genVote) | canGenVotes]
          ++ [(2, BadVote <$> genBadVote) | canGenBadVote]
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

    genVote =
      do
        block <- elements (concat allChains)
        let unequivocated v@MkVote{votingRound = r, creatorId = p} = all (\MkVote{votingRound = r', creatorId = p'} -> r /= r' || p /= p') allVotes
        flip suchThat unequivocated $
          MkVote <$> genRound <*> genPartyId <*> arbitrary <*> pure (hash block) <*> arbitrary

    badVoteCandidates = [(r, p) | MkVote r p _ _ _ <- allVotes, p /= pid modelSUT]
    canGenBadVote = canGenVotes && not (null badVoteCandidates)
    genBadVote = do
      block <- elements (concat allChains)
      (r, p) <- elements badVoteCandidates
      MkVote r p <$> arbitrary <*> pure (hash block) <*> arbitrary
    canGenVotes =
      newRound clock protocol -- Voting is only allowed in the first slot of a round.
        && not (all null allChains) -- There must be some block to vote for.
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
    validCertRounds = [1 .. r] -- \\ (round <$> Map.keys certs)
    genPartyId = choose (2, 5_000_000) `suchThat` (/= pid modelSUT)
    genRound = elements [1 .. r]
    r = inRound clock protocol

  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ (Step (NewChain (_ : chain))) = map (Some . Step) [Tick, NewChain chain]
  shrinkAction _ _ (Step _) = [Some (Step Tick)]

  precondition s (Step a) = isJust (transition s a)

  nextState s (Step a) _ = snd . fromJust $ transition s a
