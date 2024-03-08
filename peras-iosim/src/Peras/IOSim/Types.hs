{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module Peras.IOSim.Types (
  ByteSize,
  Coin,
  Rollback (..),
  VoteWithBlock,
  messageSize,
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Generic.Random (genericArbitrary, uniform)
import Numeric.Natural (Natural)
import Peras.Block (Block, Slot)
import Peras.Chain (Vote)
import Peras.Message (Message (..))
import Peras.Orphans ()
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Instances.Natural ()

type Coin = Int

type ByteSize = Word64

type VoteWithBlock = (Vote, Block)

data Rollback = Rollback
  { atSlot :: Slot
  , slots :: Natural
  , blocks :: Natural
  , fromWeight :: Double
  , toWeight :: Double
  }
  deriving stock (Eq, Generic, Ord, Read, Show)

instance FromJSON Rollback
instance ToJSON Rollback

instance Arbitrary Rollback where
  arbitrary = genericArbitrary uniform

-- | The estimated serialized size of the message, in bytes
messageSize :: Message -> Word64
messageSize = \case
  NextSlot{} -> 0
  SomeBlock{} -> 72000 -- full body size at 80% load
  NewChain{} -> 1000 -- just the size of a header, checkout https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L22
  SomeVote{} -> 300 -- FIXME
  _ -> 300 -- FIXME
