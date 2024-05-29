{-# LANGUAGE DeriveGeneric #-}

module Peras.Abstract.Protocol.Diffusion (
  Diffuser,
  allPendingChains,
  allPendingVotes,
  defaultDiffuser,
  diffuseChain,
  diffuseVote,
  insertChains,
  insertVotes,
  mergeDiffusers,
  popChainsAndVotes,
) where

import Control.Arrow ((&&&))
import Control.Concurrent.Class.MonadSTM (MonadSTM, TVar, atomically, modifyTVar', readTVar)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map (insertWith, partitionWithKey, unionWith)
import Data.Set (Set)
import qualified Data.Set as Set (singleton, union, unions)
import GHC.Generics (Generic)
import Peras.Abstract.Protocol.Types (PerasResult)
import Peras.Chain (Chain, Vote)
import Peras.Numbering (SlotNumber)
import Peras.Orphans ()

data Diffuser = MkDiffuser
  { delay :: Integer
  , pendingChains :: Map SlotNumber (Set Chain)
  , pendingVotes :: Map SlotNumber (Set Vote)
  }
  deriving (Eq, Generic, Show)

defaultDiffuser :: Integer -> Diffuser
defaultDiffuser x = MkDiffuser{delay = x, pendingChains = mempty, pendingVotes = mempty}

mergeDiffusers :: Diffuser -> Diffuser -> Diffuser
mergeDiffusers x y =
  x
    { pendingChains = (Map.unionWith Set.union `on` pendingChains) x y
    , pendingVotes = (Map.unionWith Set.union `on` pendingVotes) x y
    }

allPendingChains :: Diffuser -> Set Chain
allPendingChains = Set.unions . toList . pendingChains

allPendingVotes :: Diffuser -> Set Vote
allPendingVotes = Set.unions . toList . pendingVotes

insertChains :: SlotNumber -> Set Chain -> Diffuser -> Diffuser
insertChains slot chains diffuser =
  diffuser{pendingChains = Map.insertWith Set.union slot chains $ pendingChains diffuser}

insertVotes :: SlotNumber -> Set Vote -> Diffuser -> Diffuser
insertVotes slot votes diffuser =
  diffuser{pendingVotes = Map.insertWith Set.union slot votes $ pendingVotes diffuser}

diffuseChain :: MonadSTM m => TVar m Diffuser -> SlotNumber -> Chain -> m (PerasResult ())
diffuseChain diffuserVar slot chain =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser
        { pendingChains =
            Map.insertWith
              Set.union
              (fromIntegral $ fromIntegral slot + delay diffuser)
              (Set.singleton chain)
              $ pendingChains diffuser
        }

diffuseVote :: MonadSTM m => TVar m Diffuser -> SlotNumber -> Vote -> m (PerasResult ())
diffuseVote diffuserVar slot vote =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser
        { pendingVotes =
            Map.insertWith
              Set.union
              (fromIntegral $ fromIntegral slot + delay diffuser)
              (Set.singleton vote)
              $ pendingVotes diffuser
        }

popChainsAndVotes :: MonadSTM m => TVar m Diffuser -> SlotNumber -> m (Set Chain, Set Vote)
popChainsAndVotes diffuserVar slot =
  atomically $
    do
      let partition = Map.partitionWithKey (const . (<= slot))
      ((olderChains, newerChains), (olderVotes, newerVotes)) <-
        (partition . pendingChains &&& partition . pendingVotes)
          <$> readTVar diffuserVar
      modifyTVar' diffuserVar $ \d -> d{pendingChains = newerChains, pendingVotes = newerVotes}
      pure (Set.unions $ toList olderChains, Set.unions $ toList olderVotes)
