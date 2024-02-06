{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
module Peras.Model where

import Test.QuickCheck.StateModel(StateModel(..), Var)
import GHC.Generics (Generic)
import Data.ByteString (ByteString)

-- | We model a network of nodes interconnected through a diffusion layer.
data Network = Network
 deriving (Show, Generic)

newtype BlockId = BlockId { unBlockId :: ByteString }
  deriving (Eq, Show)

newtype NodeId = NodeId { unNodeId :: ByteString }
  deriving (Eq, Show)

newtype Block = Block { blockId :: BlockId }
 deriving (Eq, Show)

data Chain = Genesis
 | Chain Block Chain
  deriving (Eq, Show)

instance StateModel Network where

   data Action Network a where
     DispatchBlock :: Action Network (Maybe (Var Block ))

     ObserveNode :: NodeId -> Action Network Chain
