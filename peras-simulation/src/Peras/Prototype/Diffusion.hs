{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.Prototype.Diffusion (
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
import Data.Aeson (FromJSON, ToJSON)
import Data.Default (Default (..))
import Data.Foldable (toList)
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map (elems, insertWith, partitionWithKey, unionWith)
import GHC.Generics (Generic)
import Peras.Chain (Chain, Vote)
import Peras.Numbering (SlotNumber)
import Peras.Orphans ()
import Peras.Prototype.Types (PerasResult)

data Diffuser = MkDiffuser
  { delay :: Integer
  , pendingChains :: Map SlotNumber [Chain]
  , pendingVotes :: Map SlotNumber [Vote]
  }
  deriving (Eq, Generic, Show)

instance FromJSON Diffuser
instance ToJSON Diffuser

instance Default Diffuser where
  def = defaultDiffuser 0

defaultDiffuser :: Integer -> Diffuser
defaultDiffuser delay = MkDiffuser{delay, pendingChains = mempty, pendingVotes = mempty}

mergeDiffusers :: Diffuser -> Diffuser -> Diffuser
mergeDiffusers x y =
  x
    { pendingChains = (Map.unionWith (<>) `on` pendingChains) x y
    , pendingVotes = (Map.unionWith (<>) `on` pendingVotes) x y
    }

allPendingChains :: Diffuser -> [Chain]
allPendingChains = concat . Map.elems . pendingChains

allPendingVotes :: Diffuser -> [Vote]
allPendingVotes = concat . Map.elems . pendingVotes

insertChains :: SlotNumber -> [Chain] -> Diffuser -> Diffuser
insertChains slot chains diffuser =
  diffuser{pendingChains = Map.insertWith (<>) slot chains $ pendingChains diffuser}

insertVotes :: SlotNumber -> [Vote] -> Diffuser -> Diffuser
insertVotes slot votes diffuser =
  diffuser{pendingVotes = Map.insertWith (<>) slot votes $ pendingVotes diffuser}

diffuseChain :: MonadSTM m => TVar m Diffuser -> SlotNumber -> Chain -> m (PerasResult ())
diffuseChain diffuserVar slot chain =
  fmap pure
    . atomically
    . modifyTVar' diffuserVar
    $ \diffuser ->
      diffuser
        { pendingChains =
            Map.insertWith
              (<>)
              (fromIntegral $ fromIntegral slot + delay diffuser)
              (pure chain)
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
              (<>)
              (fromIntegral $ fromIntegral slot + delay diffuser)
              (pure vote)
              $ pendingVotes diffuser
        }

popChainsAndVotes :: MonadSTM m => TVar m Diffuser -> SlotNumber -> m ([Chain], [Vote])
popChainsAndVotes diffuserVar slot =
  atomically $
    do
      let partition = Map.partitionWithKey (const . (<= slot))
      ((olderChains, newerChains), (olderVotes, newerVotes)) <-
        (partition . pendingChains &&& partition . pendingVotes)
          <$> readTVar diffuserVar
      modifyTVar' diffuserVar $ \d -> d{pendingChains = newerChains, pendingVotes = newerVotes}
      pure (concat $ toList olderChains, concat $ toList olderVotes)
