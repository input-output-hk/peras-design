{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Diffusion (
  DiffuseBlock,
  diffuseBlock,
  DiffuseVote,
  diffuseVote,
) where

import Control.Concurrent.STM (atomically)
import Control.Concurrent.STM.TVar (TVar, modifyTVar')
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Set (Set)
import GHC.Generics (Generic)
import Peras.Abstract.Protocol.Types (DiffuseBlock, DiffuseVote)
import Peras.Block (Block)
import Peras.Chain (Vote)

import qualified Data.Set as Set (insert)

data Diffuser = MkDiffuser
  { pendingBlocks :: Set Block
  , pendingVotes :: Set Vote
  }
  deriving (Eq, Generic, Show)

diffuseBlock :: MonadIO m => TVar Diffuser -> DiffuseBlock m
diffuseBlock diffuserVar block =
  fmap pure
    . liftIO
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser{pendingBlocks = Set.insert block $ pendingBlocks diffuser}

diffuseVote :: MonadIO m => TVar Diffuser -> DiffuseVote m
diffuseVote diffuserVar vote =
  fmap pure
    . liftIO
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser{pendingVotes = Set.insert vote $ pendingVotes diffuser}
