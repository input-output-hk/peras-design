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

import Data.IORef
import Data.Function
import Prelude hiding (round)
import Control.Monad
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Map (Map)
import Data.Map qualified as Map
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
import Text.PrettyPrint hiding ((<>))
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Peras.Abstract.Protocol.Trace qualified as Trace

data NodeModel = MkNodeModel
  { modelSUT         :: Party
  , clock            :: SlotNumber
  , protocol         :: PerasParams
  , allChains        :: [(RoundNumber, Chain)]
  , allAcceptedCerts :: Set Certificate
  , allSeenCerts     :: Map Certificate SlotNumber
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
    Trace.NewChainAndVotes {partyId, newChains, newVotes} ->
      hang "NewChainAndVotes" 2 $ vcat $
        [ hang "Chains:" 2 $ vcat (map pPrint $ Set.toList newChains) | not $ null newChains ] ++
        [ hang "Votes:" 2 $ vcat (map pPrint $ Set.toList newVotes) | not $ null newVotes ]
    Trace.NewChainPref {newChainPref} -> hang "NewChainPref:" 2 $ pPrint newChainPref
    Trace.NewCertificatesReceived {newCertificates} ->
      hang "NewCerts:" 2 $
        vcat [ pPrint (getSlotNumber slot) <+> ":" <+> pPrint cert | (cert, slot) <- newCertificates ]
    Trace.NewCertificatesFromQuorum {partyId , newQuorums } -> "NewQuorum"
    Trace.NewCertPrime {partyId , newCertPrime } -> hang "NewCertPrime:" 2 (pPrint newCertPrime)
    Trace.NewCertStar {partyId , newCertStar } -> hang "NewCertStar:" 2 (pPrint newCertStar)
    Trace.CastVote {partyId , vote } -> hang "CastVote:" 2 (pPrint vote)
    Trace.PreagreementBlock {partyId , weight } -> "PreagreementBlock"
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

preferredChain :: PerasParams -> Set Certificate -> [Chain] -> Chain
preferredChain MkPerasParams{..} certs chains =
  maximumBy (compare `on` chainWeight perasB certs) (Set.insert genesisChain $ Set.fromList chains)

votesInState :: NodeModel -> Set Vote
votesInState MkNodeModel{protocol = protocol@MkPerasParams{..}, ..}
  | Just vote <- getVote = Set.singleton vote
  | otherwise = mempty
  where
    getVote = do
      let r = inRound clock protocol
          chains' = map snd $ filter ((< r) . fst) allChains
          -- This is to deal with the fact that the information
          -- available is out of step
          allSeenAcceptedCerts = Set.fromList
                                  [ c
                                  | c <- Set.toList allAcceptedCerts
                                  , s <- maybeToList (Map.lookup c allSeenCerts)
                                  , fromIntegral s < fromIntegral r * perasU
                                  ]
          pref  = preferredChain protocol allSeenAcceptedCerts chains'
          (cert', cert'Slot) = maximumBy (comparing snd)
                                  [ (c, s)
                                  | c <- Set.toList allSeenAcceptedCerts
                                  , s <- maybeToList (Map.lookup c allSeenCerts)
                                  ]
          certS = maximumBy (comparing round) $ [ c | MkBlock{certificate=Just c} <- pref ] ++ [genesisCert]
          party = mkCommitteeMember modelSUT protocol (clock - fromIntegral perasT) True
      guard $ mod (getSlotNumber clock) perasU == perasT
      block <- listToMaybe $ dropWhile (not . blockOldEnough) pref
      let vr1A = round cert' + 1 == r
                 && fromIntegral cert'Slot + perasΔ <= fromIntegral (r - 1) * perasU + perasU - 1
          vr1B = extends block cert' chains' -- VR-1B
          vr2A = r >= round cert' + fromIntegral perasR
          vr2B = r > round certS &&
                  0 == fromIntegral (r - round certS) `mod` perasK
          shouldVote = vr1A && vr1B || vr2A && vr2B
      guard shouldVote
      Right proof <- createMembershipProof r (Set.singleton party)
      Right vote  <- createSignedVote party r (hash block) proof 1
      pure vote
    blockOldEnough MkBlock{..} = getSlotNumber slotNumber + perasL <= getSlotNumber clock - perasT

transition :: NodeModel -> EnvAction -> Maybe (Set Vote, NodeModel)
transition s a = case a of
  Tick -> Just (votesInState s', s')
    -- TODO: here we need to turn vote quorums into certs.
    where s' = s { clock = clock s + 1 }
  NewChain chain -> Just (mempty, s { allChains = (inRound (clock s) (protocol s), chain) : allChains s
                                    , allSeenCerts =
                                        Map.unionWith min
                                          (Map.fromList [ (c, clock s) | MkBlock{certificate = Just c} <- chain ])
                                          (allSeenCerts s)
                                    , allAcceptedCerts = allAcceptedCerts s <>
                                        Set.fromList [ c | MkBlock{certificate = Just c} <- chain ]

                                    })
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
                            , allChains = [(0, genesisChain)]
                            , allAcceptedCerts = Set.singleton genesisCert
                            , allSeenCerts = Map.singleton genesisCert 0
                            }

  arbitraryAction _ MkNodeModel{modelSUT, clock, allChains, protocol} =
    fmap (Some . Step) $
      frequency $ [ (1, pure Tick) ] ++
                  [ (1, NewChain <$> genChain) ] ++
                  [ (1, NewVote  <$> genVote) | canGenVotes, False ]
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
    unless ok $ do
      monitorPost . counterexample . show $ "  -- expected:" <+> pPrint (Set.toList expected)
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
        putStrLn "-- Trace:"
        trace <- readIORef traceRef
        print $ vcat . map pPrint $ reverse trace
  pure $ whenFail printTrace
       $ monadicIO $ do
          monitor $ counterexample "do"
          _ <- runPropertyStateT (runActions @_ @(Runtime IO) as) RunState{..}
          pure True
