{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Peras.Message where

import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Base16 as Hex
import Data.Maybe (mapMaybe)
import Data.String (IsString (..))
import Data.Text (pack, unpack)
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Peras.Block (Block, BlockId, Slot)

newtype NodeId = NodeId {nodeId :: ByteString}
  deriving (Eq, Ord)

instance Show NodeId where
  show NodeId{nodeId} =
    unpack $ decodeUtf8 $ Hex.encode nodeId

instance Read NodeId where
  readsPrec n = fmap (first fromString) . readsPrec n

instance IsString NodeId where
  fromString t = case Hex.decode (encodeUtf8 $ pack t) of
    Right r -> NodeId r
    Left{} -> error $ "not a valid encoded string: " <> t

data Message votes
  = NextSlot Slot
  | RollForward (Block votes)
  | RollBack BlockId
  deriving (Eq, Show)

selectBlocks :: [Message ()] -> [Block ()]
selectBlocks = mapMaybe isRollForward

isRollForward :: Message () -> Maybe (Block ())
isRollForward = \case
  RollForward block -> Just block
  _other -> Nothing
