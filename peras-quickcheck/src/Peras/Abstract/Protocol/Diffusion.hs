{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Diffusion where

import Data.Set (Set)
import GHC.Generics (Generic)
import Peras.Abstract.Protocol.Types (DiffuseBlock, DiffuseVote)
import Peras.Block (Block)
import Peras.Chain (Vote)

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, modifyTVar')
import qualified Data.Set as Set (insert)

data Diffuser = MkDiffuser
  { pendingBlocks :: Set Block
  , pendingVotes :: Set Vote
  }
  deriving (Eq, Generic, Show)

defaultDiffuser :: Diffuser
defaultDiffuser = MkDiffuser{pendingBlocks = mempty, pendingVotes = mempty}

diffuseBlock :: MonadSTM m => TVar m Diffuser -> DiffuseBlock m
diffuseBlock diffuserVar block =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser{pendingBlocks = Set.insert block $ pendingBlocks diffuser}

diffuseVote :: MonadSTM m => TVar m Diffuser -> DiffuseVote m
diffuseVote diffuserVar vote =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser{pendingVotes = Set.insert vote $ pendingVotes diffuser}
