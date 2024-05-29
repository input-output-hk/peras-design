{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Diffusion where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, modifyTVar')
import Data.Set (Set)
import qualified Data.Set as Set (insert)
import GHC.Generics (Generic)
import Peras.Abstract.Protocol.Types (DiffuseChain, DiffuseVote)
import Peras.Chain (Chain, Vote)

data Diffuser = MkDiffuser
  { pendingChains :: Set Chain
  , pendingVotes :: Set Vote
  }
  deriving (Eq, Generic, Show)

defaultDiffuser :: Diffuser
defaultDiffuser = MkDiffuser{pendingChains = mempty, pendingVotes = mempty}

diffuseChain :: MonadSTM m => TVar m Diffuser -> DiffuseChain m
diffuseChain diffuserVar chain =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser{pendingChains = Set.insert chain $ pendingChains diffuser}

diffuseVote :: MonadSTM m => TVar m Diffuser -> DiffuseVote m
diffuseVote diffuserVar vote =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser{pendingVotes = Set.insert vote $ pendingVotes diffuser}
