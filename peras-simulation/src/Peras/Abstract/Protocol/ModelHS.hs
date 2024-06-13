{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

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
module Peras.Abstract.Protocol.ModelHS where

import Control.Monad.Identity
import Data.Function
import Prelude hiding (round)
import Control.Monad
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Ord
import Data.List
import Data.Maybe
import Data.Foldable ()
import Data.Default
import Peras.Chain
import Peras.Block
import Peras.Crypto
import Peras.Numbering
import Peras.Arbitraries ()
import Peras.Abstract.Protocol.Types
import Peras.Abstract.Protocol.Params
import Peras.Abstract.Protocol.Fetching
import Peras.Abstract.Protocol.Crypto
import Peras.Abstract.Protocol.Voting
import Test.QuickCheck.StateModel

data NodeModel = MkNodeModel
  { modelSUT         :: Party
  , clock            :: SlotNumber
  , protocol         :: PerasParams
  , allChains        :: [(RoundNumber, Chain)]
  , allVotes         :: Set Vote
  , allSeenCerts     :: Map Certificate SlotNumber
  }
  deriving (Eq, Show)

data EnvAction = Tick | NewChain Chain | NewVote Vote
  deriving (Show, Eq, Generic)

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
                                  | (c, s) <- Map.toList allSeenCerts
                                  , fromIntegral s <= fromIntegral r * perasU
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
                 && fromIntegral cert'Slot + perasΔ <= fromIntegral r * perasU - 1
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
  Tick -> Just (sutVotes, s' { allVotes = votes'
                             , allSeenCerts = Map.unionWith min (allSeenCerts s')
                                                                (Map.fromList (map (,clock s') newCerts))
                             } )
    where s' = s { clock = clock s + 1 }
          sutVotes = votesInState s'
          votes' = allVotes s' <> sutVotes
          newQuora = findNewQuora (fromIntegral $ perasτ $ protocol s) (Map.keysSet $ allSeenCerts s) (allVotes s')
          Identity newCertsResults = mapM (createSignedCertificate $ modelSUT s) newQuora
          newCerts = [ c | Right c <- newCertsResults ]
  NewChain chain -> Just (mempty, s { allChains = (inRound (clock s) (protocol s), chain) : allChains s
                                    , allSeenCerts =
                                        Map.unionWith min
                                          (Map.fromList [ (c, clock s + 1) | MkBlock{certificate = Just c} <- chain ])
                                          (allSeenCerts s)
                                    })
  NewVote v -> Just (mempty, s { allVotes = Set.insert v $ allVotes s })

initialModelState :: NodeModel
initialModelState =
  MkNodeModel{ modelSUT = mkParty 1 mempty [0..10_000] -- Never the slot leader, always a committee member
             , clock = systemStart + 1
             -- NOTE: this model tends to break as you change these. That's an interesting
             -- piece of information that we should deal with later. Important focus now is
             -- connecting this to agda.
             , protocol = def { perasU = 5
                              , perasR = 1
                              , perasK = 1
                              , perasL = 1
                              , perasT = 1
                              , perasΔ = 1
                              , perasτ = 1
                              }
             , allChains = [(0, genesisChain)]
             , allVotes = mempty
             , allSeenCerts = Map.singleton genesisCert 0
             }
