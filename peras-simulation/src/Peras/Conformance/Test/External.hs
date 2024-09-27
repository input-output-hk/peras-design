{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Peras.Conformance.Test.External where

import Control.Monad (unless, void, when)
import Control.Monad.IO.Class ()
import Control.Monad.State (
  MonadState (get),
  MonadTrans (lift),
  StateT,
  modify,
 )
import Data.Aeson (FromJSON, ToJSON)
import Data.Aeson qualified as A
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Default (Default (def))
import Data.List (sort)
import GHC.Generics (Generic)
import Peras.Block (Certificate, Party)
import Peras.Chain (Chain, Vote (..))
import Peras.Conformance.Model (
  EnvAction (..),
  NodeModel (..),
  initialModelState,
  sutId,
  transition,
 )
import Peras.Conformance.Params (PerasParams)
import Peras.Conformance.Test (
  Action (Initial, Step),
  NetworkModel (NetworkModel, nodeModel),
  sortition,
 )
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber)
import Peras.Prototype.Crypto (
  IsCommitteeMember,
  IsSlotLeader,
  mkParty,
 )
import Peras.Prototype.Types (
  inRound,
  newRound,
 )
import System.IO (Handle)
import Test.QuickCheck (
  Blind (Blind),
  Property,
  counterexample,
  ioProperty,
  noShrinking,
 )
import Test.QuickCheck.Extras (runPropertyStateT)
import Test.QuickCheck.Monadic (monadicIO, monitor)
import Test.QuickCheck.StateModel (
  Actions,
  Realized,
  RunModel (perform, postcondition),
  counterexamplePost,
  monitorPost,
  runActions,
 )
import Text.PrettyPrint (hang, (<+>))
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))
import Prelude hiding (round)

data NodeRequest
  = Initialize
      { party :: Party
      , slotNumber :: SlotNumber
      , parameters :: PerasParams
      , chainsSeen :: [Chain]
      , votesSeen :: [Vote]
      , certsSeen :: [Certificate]
      }
  | Tick
  | Fetching
      { newChains :: [Chain]
      , newVotes :: [Vote]
      }
  | BlockCreation
      { isSlotLeader :: IsSlotLeader
      }
  | Voting
      { isCommitteeMember :: IsCommitteeMember
      }
  | NewSlot
      { isSlotLeader :: IsSlotLeader
      , isCommitteeMember :: IsCommitteeMember
      , newChains :: [Chain]
      , newVotes :: [Vote]
      }
  | Stop
  deriving (Eq, Generic, Show)

instance FromJSON NodeRequest
instance ToJSON NodeRequest

data NodeResponse
  = NodeResponse
      { diffuseChains :: [Chain]
      , diffuseVotes :: [Vote]
      }
  | Failed
      { failure :: String
      }
  | Stopped
  deriving (Eq, Generic, Show)

instance Default NodeResponse where
  def = NodeResponse mempty mempty

instance FromJSON NodeResponse
instance ToJSON NodeResponse

data RunState = RunState
  { hReader :: Handle
  , hWriter :: Handle
  , unfetchedChains :: [Chain]
  , unfetchedVotes :: [Vote]
  }

callSUT ::
  RunState -> NodeRequest -> IO NodeResponse
callSUT RunState{hReader, hWriter} req =
  do
    -- Verified that this writes UTF-8.
    LBS8.hPutStrLn hWriter $ A.encode req
    -- Verified that this reads UTF-8.
    either Failed id . A.eitherDecode' . LBS.fromStrict <$> BS8.hGetLine hReader

type Runtime = StateT RunState IO

instance Realized IO ([Chain], [Vote]) ~ ([Chain], [Vote]) => RunModel NetworkModel Runtime where
  perform NetworkModel{nodeModel = NodeModel{..}} (Initial params leaderSlots voterRounds) _ =
    do
      rs <- get
      void . lift $
        callSUT
          rs
          Initialize
            { party = mkParty sutId leaderSlots voterRounds
            , slotNumber = clock
            , parameters = params
            , chainsSeen = allChains
            , votesSeen = allVotes
            , certsSeen = allSeenCerts
            }
  perform net@NetworkModel{nodeModel = NodeModel{..}} (Step a) _ = case a of
    Peras.Conformance.Model.Tick -> do
      rs@RunState{..} <- get
      modify $ \rs' -> rs'{unfetchedChains = mempty, unfetchedVotes = mempty}
      let clock' = clock + 1
          (isSlotLeader', isCommitteeMember') = sortition net
      lift
        ( callSUT
            rs
            NewSlot
              { isSlotLeader = isSlotLeader' clock'
              , isCommitteeMember = isCommitteeMember' $ inRound clock' protocol
              , newChains = unfetchedChains
              , newVotes = unfetchedVotes
              }
        )
        >>= \case
          NodeResponse{..} -> pure (diffuseChains, diffuseVotes)
          _ -> pure (mempty, mempty) -- FIXME: The state model should define an error type.
    NewChain c -> do
      modify $ \rs -> rs{unfetchedChains = unfetchedChains rs ++ pure c}
      pure (mempty, mempty)
    NewVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure (mempty, mempty)
    BadVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure (mempty, mempty)

  postcondition _ Initial{} _ () = pure True
  postcondition (net@NetworkModel{nodeModel = s}, NetworkModel{nodeModel = s'}) (Step a) _ (cs, vs) = do
    let (expectedChains, expectedVotes) = maybe (mempty, mempty) fst $ transition (sortition net) s a
    let eqVotes vs0 vs1 =
          let f MkVote{..} = (votingRound, creatorId, blockHash)
           in sort (f <$> vs0) == sort (f <$> vs1)
        eqChains cs0 cs1 = cs0 == cs1
    let ok = eqChains cs expectedChains && eqVotes vs expectedVotes
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Peras.Conformance.Model.Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $
        "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (eqChains cs expectedChains) $ do
      monitorPost . counterexample . show $ "  --      got chains:" <+> pPrint cs
      monitorPost . counterexample . show $ "  --      expected chains:" <+> pPrint expectedChains
    unless (eqVotes vs expectedVotes) $ do
      monitorPost . counterexample . show $ "  --      got votes:" <+> pPrint vs
      monitorPost . counterexample . show $ "  --      expected votes:" <+> pPrint expectedVotes
    counterexamplePost . show $ "  " <> hang "-- model state before:" 2 (pPrint net)
    pure ok

prop_node :: Handle -> Handle -> Blind (Actions NetworkModel) -> Property
prop_node hReader hWriter (Blind as) = noShrinking $
  ioProperty $ do
    let unfetchedChains = mempty
        unfetchedVotes = mempty
    callSUT
      RunState{..}
      Initialize
        { party = mkParty sutId mempty mempty
        , slotNumber = clock initialModelState
        , parameters = protocol initialModelState
        , chainsSeen = allChains initialModelState
        , votesSeen = allVotes initialModelState
        , certsSeen = allSeenCerts initialModelState
        }
      >>= \case
        NodeResponse{} ->
          pure $
            monadicIO $ do
              monitor $ counterexample "-- Actions:"
              monitor $ counterexample "do"
              _ <- runPropertyStateT (runActions @_ @Runtime as) RunState{..}
              pure True
        _ -> pure $ monadicIO $ pure False
