{-# LANGUAGE NamedFieldPuns #-}

module Peras.RandomForks (
  run
, advance
) where

import Control.Monad.IO.Class (MonadIO(..))
import Data.Bifunctor (bimap)
import Data.Foldable (foldlM)
import Peras.RandomForks.Chain (Message(Message, messageDestination))
import Peras.RandomForks.IO.Graphviz (chainGraph, writeGraph)
import Peras.RandomForks.Peer (PeerState(pendingMessages, preferredChain), Peers(..), nextSlot)
import Peras.RandomForks.Protocol (Protocol)
import Peras.RandomForks.Types (Slot) 
import System.FilePath ((<.>))
import System.Random.Stateful (StatefulGen)

import qualified Data.Map.Strict as M

run
  :: MonadIO m
  => StatefulGen g m
  => g
  -> Protocol
  -> Maybe FilePath
  -> Peers
  -> Int
  -> m Peers
run gen protocol baseName peers duration =
  foldlM (advance gen protocol baseName) peers [0..duration]
  
advance
  :: MonadIO m
  => StatefulGen g m
  => g
  -> Protocol
  -> Maybe FilePath
  -> Peers
  -> Slot
  -> m Peers
advance gen protocol baseName (Peers peers) slot =
  do
    -- Advance one slot.
    (peers', messages) <-
      bimap M.fromList mconcat . unzip
        <$> sequence
        [
          do
            (state', messages) <- nextSlot gen protocol slot name state
            pure ((name, state'), messages)
        |
          (name, state) <- M.toList peers  -- FIXME: Rewrite as map.
        ]
    -- Deliver any new messages.
    let
      deliverMessage ps message@Message{messageDestination} =
        M.adjust (\state -> state {pendingMessages = pendingMessages state <> pure message}) messageDestination ps
      peers'' = foldl deliverMessage peers' messages
    liftIO $ maybe (pure ()) (flip writeGraph (chainGraph $ preferredChain <$> M.elems peers'') . (<.> "dot") . (<> show slot)) baseName
    pure $ Peers peers''
