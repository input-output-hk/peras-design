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

import Control.Concurrent.Class.MonadSTM (MonadSTM (TVar))
import Control.Concurrent.STM.TVar qualified as IO
import Control.Monad (unless, void, when)
import Control.Monad.IO.Class ()
import Control.Monad.State (
  MonadState (get),
  MonadTrans (lift),
  StateT,
  modify,
 )
import Control.Tracer (Tracer (Tracer), emit, nullTracer)
import Data.Aeson (FromJSON, ToJSON)
import Data.Aeson qualified as A
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Default (Default (def))
import Data.IORef (modifyIORef, newIORef, readIORef)
import Data.List (sort)
import Data.Maybe (fromJust)
import Data.Set (Set)
import GHC.Generics (Generic)
import Peras.Block (Certificate, Party)
import Peras.Chain (Chain, Vote (..))
import Peras.Conformance.Model (
  EnvAction (BadVote, NewChain, NewVote, Tick),
  NodeModel (..),
  initialModelState,
  transition,
 )
import Peras.Conformance.Params (PerasParams)
import Peras.Conformance.Test (Action (Step), modelSUT)
import Peras.Numbering (RoundNumber (getRoundNumber), SlotNumber)
import Peras.Prototype.BlockSelection (selectBlock)
import Peras.Prototype.Crypto (
  IsCommitteeMember,
  IsSlotLeader,
  isCommitteeMember,
  isSlotLeader,
  mkCommitteeMember,
 )
import Peras.Prototype.Diffusion (
  Diffuser,
  diffuseVote,
  popChainsAndVotes,
 )
import Peras.Prototype.Fetching (fetching)
import Peras.Prototype.Trace qualified as Trace
import Peras.Prototype.Types (
  PerasState,
  inRound,
  initialPerasState,
  newRound,
 )
import Peras.Prototype.Voting (voting)
import System.IO (Handle, IO)
import Test.QuickCheck (
  Blind (Blind),
  Property,
  counterexample,
  ioProperty,
  noShrinking,
  whenFail,
 )
import Test.QuickCheck.DynamicLogic (DynLogicModel)
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
import Text.PrettyPrint (hang, vcat, (<+>))
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

instance Realized IO [Vote] ~ [Vote] => RunModel NodeModel Runtime where
  perform NodeModel{..} (Step a) _ = case a of
    Peras.Conformance.Model.Tick -> do
      rs@RunState{..} <- get
      modify $ \rs -> rs{unfetchedChains = mempty, unfetchedVotes = mempty}
      let clock' = clock + 1
      ( lift $
          callSUT
            rs
            NewSlot
              { isSlotLeader = Peras.Prototype.Crypto.isSlotLeader modelSUT clock'
              , isCommitteeMember = Peras.Prototype.Crypto.isCommitteeMember modelSUT (inRound clock' protocol)
              , newChains = unfetchedChains
              , newVotes = unfetchedVotes
              }
        )
        >>= \case
          NodeResponse{..} -> pure diffuseVotes
          _ -> pure mempty -- FIXME: The state model should define an error type.
    NewChain c -> do
      modify $ \rs -> rs{unfetchedChains = unfetchedChains rs ++ pure c}
      pure mempty
    NewVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty
    BadVote v -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure v}
      pure mempty

  postcondition (s, s') (Step a) _ r = do
    let expected = fst (fromJust (transition s a))
    let eqVotes vs vs' =
          let f MkVote{..} = (votingRound, creatorId, blockHash)
           in sort (f <$> vs) == sort (f <$> vs')
    let ok = r `eqVotes` expected
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Peras.Conformance.Model.Tick && newRound (clock s') (protocol s')) $
      monitorPost . counterexample $
        "  -- round: " ++ show (getRoundNumber $ inRound (clock s') (protocol s'))
    unless (null r) $ do
      monitorPost . counterexample . show $ "  --      got:" <+> pPrint r
    counterexamplePost . show $ "  -- expected:" <+> pPrint expected
    counterexamplePost . show $ "  " <> hang "-- model state before:" 2 (pPrint s)
    pure ok

prop_node :: Handle -> Handle -> Blind (Actions NodeModel) -> Property
prop_node hReader hWriter (Blind as) = noShrinking $
  ioProperty $ do
    let unfetchedChains = mempty
        unfetchedVotes = mempty
    callSUT
      RunState{..}
      Initialize
        { party = modelSUT
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
