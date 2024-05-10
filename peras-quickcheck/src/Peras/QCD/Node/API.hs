{-# LANGUAGE MultiParamTypeClasses #-}

module Peras.QCD.Node.API (
  PerasNode (..),
) where

import Peras.QCD.Protocol (Params)
import Peras.QCD.Types (Chain, Message, PartyId, Tx, Vote, Weight)

class Monad m => PerasNode a m where
  initialize :: Params -> PartyId -> a -> m ([Message], a)
  fetching :: [Chain] -> [Vote] -> a -> m ([Message], a)
  blockCreation :: [Tx] -> a -> m ([Message], a)
  voting :: Weight -> a -> m ([Message], a)
