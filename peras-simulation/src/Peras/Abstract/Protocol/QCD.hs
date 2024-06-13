{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
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
{-# OPTIONS_GHC -fno-warn-orphans  #-}
module Peras.Abstract.Protocol.QCD where

import Peras.Abstract.Protocol.ModelHS
import Data.IORef
import Data.Function
import Prelude hiding (round)
import Control.Monad
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Map qualified as Map
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
import Text.PrettyPrint hiding ((<>))
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Peras.Abstract.Protocol.Trace qualified as Trace

instance HasVariables NodeModel where
  getAllVariables _ = mempty

instance Show (Action NodeModel a) where
  show (Step a) = show a
deriving instance Eq (Action NodeModel a)

instance HasVariables (Action NodeModel a) where
  getAllVariables _ = mempty

instance Pretty NodeModel where
  pPrint MkNodeModel{..} =
    hang "NodeModel" 2 $ braces $ vcat
      [ hang "clock =" 2 $ pPrint (getSlotNumber clock)
      , hang "allChains =" 2 $ vcat [ pPrint (getRoundNumber r) <+> ":" <+> pPrint c
                                    | (r, c) <- allChains
                                    ]
      , hang "allVotes =" 2 $ pPrint (Set.toList allVotes)
      , hang "allSeenCerts =" 2 $ vcat [ pPrint (getSlotNumber s) <+> ":" <+> pPrint c
                                       | (c, s) <- Map.toList allSeenCerts ]
      ]

instance Pretty EnvAction where
  pPrint Tick = "Tick"
  pPrint (NewChain chain) =
    "NewChain" <+> pPrint chain
  pPrint (NewVote vote) = "NewVote" <+> pPrintPrec prettyNormal 10 vote

instance Pretty Block where
  pPrint MkBlock{..} =
    "Block" <+> braces (vcat [ "hash    =" <+> text (show signature)
                             , "slot    =" <+> pPrint (getSlotNumber slotNumber)
                             , "creator =" <+> pPrint creatorId
                             , "parent  =" <+> text (show parentBlock)
                             , "cert    =" <+> pPrint certificate
                             ])

instance Pretty Certificate where
  pPrintPrec _ d MkCertificate{..} =
    maybeParens (d > 0) $ "Cert" <+> pPrint (getRoundNumber round) <+> text (show blockRef)

instance Pretty Vote where
  pPrintPrec _ d MkVote{..} =
    maybeParens (d > 0) $ "Vote" <+> braces (vcat [ "round     =" <+> pPrint (getRoundNumber votingRound)
                                                  , "creator   =" <+> pPrint creatorId
                                                  , "blockHash =" <+> text (show blockHash)
                                                  , "proofM    =" <+> text (show proofM)
                                                  , "signature =" <+> text (show signature)
                                                  ])


instance Pretty Trace.PerasLog where
  pPrint = \case
    Trace.Protocol{} -> "Protocol"
    Trace.Tick {} -> "Tick"
    Trace.NewChainAndVotes {newChains, newVotes} ->
      hang "NewChainAndVotes" 2 $ vcat $
        [ hang "Chains:" 2 $ vcat (map pPrint $ Set.toList newChains) | not $ null newChains ] ++
        [ hang "Votes:" 2 $ vcat (map pPrint $ Set.toList newVotes) | not $ null newVotes ]
    Trace.NewChainPref {newChainPref} -> hang "NewChainPref:" 2 $ pPrint newChainPref
    Trace.NewCertificatesReceived {newCertificates} ->
      hang "NewCerts:" 2 $
        vcat [ pPrint (getSlotNumber slot) <+> ":" <+> pPrint cert | (cert, slot) <- newCertificates ]
    Trace.NewCertificatesFromQuorum {newQuorums} ->
      hang "NewQuorums:" 2 $ pPrint newQuorums
    Trace.NewCertPrime {newCertPrime} -> hang "NewCertPrime:" 2 (pPrint newCertPrime)
    Trace.NewCertStar {newCertStar} -> hang "NewCertStar:" 2 (pPrint newCertStar)
    Trace.CastVote {vote} -> hang "CastVote:" 2 (pPrint vote)
    Trace.PreagreementBlock {block} -> hang "PreagreementBlock:" 2 $ pPrint block
    Trace.PreagreementNone {} -> "PreagreementNone"
    Trace.ForgingLogic {} -> "ForgingLogic"
    Trace.VotingLogic {vr1a, vr1b, vr2a, vr2b } ->
      hang "VotingLogic:" 2 $ vcat [ "VR-1A =" <+> pPrint vr1a
                                   , "VR-1B =" <+> pPrint vr1b
                                   , "VR-2A =" <+> pPrint vr2a
                                   , "VR-2B =" <+> pPrint vr2b
                                   ]
    Trace.DiffuseChain {chain} ->
      hang "DiffuseChain:" 2 $ pPrint chain
    Trace.DiffuseVote {vote } ->
      hang "DiffuseVote" 2 $ pPrint vote

instance StateModel NodeModel where
  data Action NodeModel a where
    Step :: EnvAction -> Action NodeModel (Set Vote)

  initialState = initialModelState

  arbitraryAction _ MkNodeModel{modelSUT, clock, allChains, protocol} =
    fmap (Some . Step) $
      frequency $ [ (1, pure Tick) ] ++
                  [ (1, NewChain <$> genChain) ] ++
                  [ (1, NewVote  <$> genVote) | canGenVotes ]
    where
      genChain =
        do
          tip' <- elements $ map snd allChains
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
          block <- elements (concat $ map snd allChains)
          MkVote <$> genRound <*> genPartyId <*> arbitrary <*> pure (hash block) <*> arbitrary
      canGenVotes =
        newRound clock protocol -- Voting is only allowed in the first slot of a round.
          && not (all (null . snd) allChains) -- There must be some block to vote for.
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
      genPartyId = arbitrary `suchThat` (/= pid modelSUT)
      genRound = elements [1 .. r]
      r = inRound clock protocol

  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ (Step (NewChain (_:chain))) = map (Some . Step) [Tick, NewChain chain]
  shrinkAction _ _ (Step _) = [Some (Step Tick)]

  precondition s (Step a) = isJust (transition s a)

  nextState s (Step a) _ = snd . fromJust $ transition s a

data RunState m =
  RunState { stateVar        :: TVar m PerasState
           , diffuserVar     :: TVar m Diffuser
           , tracer          :: Tracer m Trace.PerasLog
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
        _ <- fetching tracer protocol modelSUT stateVar clock' unfetchedChains unfetchedVotes
        let party = mkCommitteeMember modelSUT protocol clock' True
            preagreement' = preagreement nullTracer
            diffuser = diffuseVote diffuserVar
        _ <- voting tracer protocol party stateVar (inRound clock' protocol) preagreement' diffuser
        snd <$> popChainsAndVotes diffuserVar clock'
    NewChain c -> do
      modify $ \ rs -> rs { unfetchedChains = Set.insert c (unfetchedChains rs) }
      pure mempty
    NewVote v -> do
      modify $ \ rs -> rs { unfetchedVotes = Set.insert v (unfetchedVotes rs) }
      pure mempty

  postcondition (s, s') (Step a) _ r = do
    let expected = fromJust $ fmap fst (transition s a)
    -- let ok = length r == length expected
    let ok = r == expected
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $ "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (null r) $ do
      monitorPost . counterexample . show $ "  --      got:" <+> pPrint (Set.toList r)
    counterexamplePost . show $ "  -- expected:" <+> pPrint (Set.toList expected)
    counterexamplePost . show $ "  " <> hang "-- model state before:" 2 (pPrint s)
    pure ok

prop_node :: Blind (Actions NodeModel) -> Property
prop_node (Blind as) = ioProperty $ do
  stateVar <- IO.newTVarIO initialPerasState
  diffuserVar <- IO.newTVarIO def
  traceRef <- newIORef []
  let unfetchedChains = mempty
      unfetchedVotes = mempty
      tracer = Tracer $ emit $ \ a -> modifyIORef traceRef (a:)
      printTrace = do
        putStrLn "-- Trace from node:"
        trace <- readIORef traceRef
        print $ vcat . map pPrint $ reverse trace
  pure $ whenFail printTrace
       $ monadicIO $ do
          monitor $ counterexample "-- Actions:"
          monitor $ counterexample "do"
          _ <- runPropertyStateT (runActions @_ @(Runtime IO) as) RunState{..}
          pure True
