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

import Control.Monad (when)
import Data.Function (on)
import Data.List (nubBy)
import Data.Maybe (isJust)
import Peras.Arbitraries ()
import Peras.Block (Block (..), Certificate (..), Party)
import Peras.Chain (Chain, Vote (..))
import Peras.Conformance.Generators (
  GenConstraints (
    MkGenConstraints,
    selectionObeyAge,
    selectionObeyChain,
    twoParties,
    useTestParams,
    voteCurrent,
    voteObeyVR1A,
    voteObeyVR1B,
    voteObeyVR2A,
    voteObeyVR2B
  ),
  actionsSizeScaling,
  genCommitteeMembership,
  genHonestTick,
  genMutatedBlock,
  genProtocol,
  genSlotLeadership,
  genVote,
  lenientGenConstraints,
  rollbackNodeModel,
  strictGenConstraints,
 )
import Peras.Conformance.Model (
  EnvAction (..),
  NodeModel (..),
  SutIsSlotLeader,
  SutIsVoter,
  checkVotingRules,
  initialModelState,
  newQuora,
  pref,
  sutId,
  transition,
  votingBlockHash,
 )
import Peras.Conformance.Model qualified as Model
import Peras.Conformance.Params (PerasParams (perasU, perasτ))
import Peras.Crypto (Hashable (hash))
import Peras.Foreign qualified as Foreign
import Peras.Numbering (
  RoundNumber (getRoundNumber),
  SlotNumber (getSlotNumber),
  slotToRound,
 )
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Trace qualified as Trace
import Peras.Prototype.Types (inRound, newRound)
import Test.QuickCheck (
  Arbitrary (arbitrary),
  choose,
  elements,
  suchThat,
  tabulate,
 )
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.Gen (scale)
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
  show (Initial params _ _) = "Initial (" <> show params <> ")"
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
  pPrint (BadChain chain) = "BadVote" <+> pPrintPrec prettyNormal 10 chain
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
    Trace.Snapshot s -> hang "Final state" 2 $ pPrint $ show s

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
      , initialized = useTestParams lenientGenConstraints
      }

  arbitraryAction _ NetworkModel{nodeModel = s@NodeModel{clock, allChains, allVotes, protocol}, gen, initialized} =
    if initialized
      then do
        v <-
          if canGenVotes && newRound clock protocol
            then genVote gen s
            else pure Nothing
        c <- BadChain <$> genBadChain
        b <- BadVote <$> genBadVote
        fBad <- (<= 0.10) <$> choose (0, 1 :: Double)
        (newChains, newVotes) <- fst <$> genHonestTick True gen s
        fmap (Some . Step) . elements $
          [Tick]
            ++ (NewChain <$> newChains)
            ++ cleanVotes (NewVote <$> newVotes <> maybe mempty pure v)
            ++ [c | canGenBadChain && fBad]
            ++ [b | canGenBadVote && fBad]
      else scale (`div` actionsSizeScaling) $
        fmap Some $
          do
            params <- genProtocol gen
            let slotLimit = 10_000
                roundLimit = fromIntegral $ fromIntegral slotLimit `div` perasU params
            Initial params
              <$> genSlotLeadership 0.30 slotLimit
              <*> genCommitteeMembership 0.95 roundLimit
   where
    equivocated MkVote{votingRound = r0, creatorId = p} MkVote{votingRound = r1, creatorId = p'} = r0 == r1 && p == p'
    cleanVotes =
      nubBy
        ( \a a' ->
            case (a, a') of
              (NewVote v, NewVote v') -> equivocated v v'
              _ -> False
        )
        . filter
          ( \case
              NewVote v -> not $ any (equivocated v) allVotes
              _ -> True
          )

    badVoteCandidates = [(r', p) | MkVote r' p _ _ _ <- allVotes, p /= sutId]
    canGenBadVote = canGenVotes && not (null badVoteCandidates)
    genBadVote = do
      block <- elements (concat allChains)
      (r', p) <- elements badVoteCandidates
      MkVote r' p <$> arbitrary <*> pure (hash block) <*> arbitrary
    canGenVotes =
      not (all null allChains) -- There must be some block to vote for.
        && r > 0 -- No voting is allowed in the zeroth round.
        && checkVotingRules' gen s
    canGenBadChain = not $ all null allChains
    genBadChain = do
      elements allChains `suchThat` (not . null)
        >>= \case
          block : rest -> (: rest) <$> genMutatedBlock gen block
          _ -> error "Impossible."
    r = inRound clock protocol

  shrinkAction _ _ Initial{} = []
  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ (Step (NewChain (_ : chain))) = Some . Step <$> [Tick, NewChain chain]
  shrinkAction _ _ Step{} = [Some (Step Tick)]

  precondition NetworkModel{initialized} Initial{} = not initialized
  precondition _ (Step (NewChain [])) = False
  precondition NetworkModel{nodeModel = s, gen} (Step (NewVote v)) =
    voteCurrent gen `implies` (slotToRound (protocol s) (clock s) == votingRound v)
      && Foreign.checkSignedVote v
      && twoParties gen `implies` Model.checkVoteFromOther v
      && checkVotingRules' gen s
      && (selectionObeyChain gen && selectionObeyAge gen) `implies` (votingBlockHash s == blockHash v)
  precondition net@NetworkModel{nodeModel = s} (Step a) = isJust $ transition (sortition net) s a

  nextState net@NetworkModel{nodeModel = s} (Initial params slots rounds) _ =
    net{nodeModel = s{protocol = params}, leadershipSlots = slots, voterRounds = rounds, initialized = True}
  nextState net@NetworkModel{nodeModel = s, gen} (Step (NewVote v)) _ =
    if voteCurrent gen `implies` (slotToRound (protocol s) (clock s) == votingRound v)
      && Foreign.checkSignedVote v
      && twoParties gen `implies` Model.checkVoteFromOther v
      && checkVotingRules' gen s
      && (selectionObeyChain gen && selectionObeyAge gen) `implies` (votingBlockHash s == blockHash v)
      then net{nodeModel = Model.addVote' s v}
      else net
  nextState net@NetworkModel{nodeModel = s} (Step a) _ =
    net{nodeModel = maybe s snd $ transition (sortition net) s a}

checkVotingRules' :: GenConstraints -> NodeModel -> Bool
checkVotingRules' MkGenConstraints{voteObeyVR1A, voteObeyVR1B, voteObeyVR2A, voteObeyVR2B} s' =
  let
    -- FIXME: Evaluate whether we need this.
    s = backoff s'
   in
    voteObeyVR1A `implies` Model.vr1A s
      && voteObeyVR1B `implies` Model.vr1B s
      || voteObeyVR2A `implies` Model.vr2A s
        && voteObeyVR2B `implies` Model.vr2B s

backoff :: NodeModel -> NodeModel
backoff = snd . rollbackNodeModel 1

implies :: Bool -> Bool -> Bool
implies x y = not x || y

monitorChain :: Monad m => NetworkModel -> NetworkModel -> PostconditionM m ()
monitorChain net@NetworkModel{nodeModel = s} NetworkModel{nodeModel = s'@NodeModel{clock}} =
  do
    monitorPost $ tabulate "Slots (cumulative, rounded down)" [show $ (* 25) . (`div` 25) $ (fromIntegral clock :: Integer)]
    monitorPost $ tabulate "Slot leader" [show $ fst (sortition net) clock]
    monitorPost $ tabulate "Preferred chain length (cumulative, rounded down)" [show $ (* 25) . (`div` 25) $ length $ pref s']
    monitorPost $ tabulate "Preferred chain lengthens" [show $ on (>) (length . pref) s' s]

monitorCerts :: Monad m => NetworkModel -> NetworkModel -> PostconditionM m ()
monitorCerts NetworkModel{nodeModel = s} NetworkModel{nodeModel = s'} =
  do
    monitorPost $ tabulate "Certs found or created during fetching (max one per round)" [show $ on (-) (length . allSeenCerts) s' s]
    monitorPost $ tabulate "New quora" [show $ length $ newQuora (fromIntegral (perasτ (protocol s))) (allSeenCerts s) (allVotes s')]
    monitorPost $ tabulate "Certs on preferred chain (cumulative)" [show $ length $ filter (isJust . certificate) $ pref s']
    monitorPost $ tabulate "Certs created (cumulative, rounded down)" [show $ (* 1) . (`div` 1) $ length $ allSeenCerts s']

monitorVoting :: Monad m => NetworkModel -> EnvAction -> PostconditionM m ()
monitorVoting net@NetworkModel{nodeModel = s@NodeModel{clock, protocol}} a =
  do
    when (newRound clock protocol) $
      monitorPost $
        tabulate "NewVote during voting" [show $ case a of NewVote _ -> True; _ -> False]
    when (newRound (clock + 1) protocol) $
      do
        monitorPost $ tabulate "Committee member" [show $ snd (sortition net) r | let r = inRound (clock + 1) protocol]
        monitorPost $ tabulate "VR-1A/1B/2A/2B" [init . tail $ show (Model.vr1A s', Model.vr1B s', Model.vr2A s', Model.vr2B s')]
        monitorPost $ tabulate "Voting rules" [show $ checkVotingRules s']
        monitorPost $ tabulate "Does vote" [show $ maybe 0 (length . snd . fst) $ transition (sortition net) s Tick]
        monitorPost $ tabulate "Rounds (cumulative, rounded down)" [show $ (* 1) . (`div` 1) . (`div` perasU protocol) $ fromIntegral clock]
 where
  s' = s{clock = clock + 1}
