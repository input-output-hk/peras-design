{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Orphans where

import Data.Bifunctor (first)
import Data.String (IsString (..))
import GHC.Generics (Generic)
import Peras.Block (Block (..))
import Peras.Chain (Chain (..), RoundNumber (..), Vote (..))
import Peras.Crypto (Hash (..), LeadershipProof (..), MembershipProof (..), Signature (..), VerificationKey (..))
import Peras.Message (Message (..), NodeId (..))

import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Text as T
import Text.Read (Read (readPrec))

-- Only used for deriving instances of similar types.
newtype Bytes = Bytes {getBytes :: BS.ByteString}

instance Read Bytes where
  readPrec = do
    Right bs <- B16.decode . BS8.pack <$> readPrec
    pure $ Bytes bs

instance Show Bytes where
  show = show . BS8.unpack . B16.encode . getBytes

instance IsString Bytes where
  fromString = either error Bytes . B16.decode . BS8.pack

instance A.FromJSON Bytes where
  parseJSON = A.withText "Base 16 Bytes" $ either A.parseFail (pure . Bytes) . B16.decode . BS8.pack . T.unpack

instance A.ToJSON Bytes where
  toJSON = A.String . T.pack . init . tail . show

deriving stock instance Generic Block
deriving stock instance Ord Block
deriving stock instance Read Block
deriving stock instance Show Block

instance A.FromJSON Block where
  parseJSON =
    A.withObject "Block" $
      \o ->
        do
          slotNumber <- o A..: "slotNo"
          creatorId <- o A..: "creatorId"
          parentBlock <- o A..: "parentBlock"
          includedVotes <- o A..: "includedVotes"
          leadershipProof <- o A..: "leadershipProof"
          payload <- o A..: "payload"
          signature <- o A..: "signature"
          pure Block{..}

instance A.ToJSON Block where
  toJSON Block{..} =
    A.object
      [ "slotNo" A..= slotNumber
      , "creatorId" A..= creatorId
      , "parentBlock" A..= parentBlock
      , "includedVotes" A..= includedVotes
      , "leadershipProof" A..= leadershipProof
      , "payload" A..= payload
      , "signature" A..= signature
      ]

deriving stock instance Generic RoundNumber
deriving stock instance Ord RoundNumber
deriving stock instance Read RoundNumber
deriving stock instance Show RoundNumber

instance A.ToJSONKey (Maybe Block) where
  toJSONKey =
    A.toJSONKeyText $
      \case
        Nothing -> ""
        Just Block{signature = s} -> T.pack . BS8.unpack . B16.encode $ Peras.Crypto.signature s

instance A.FromJSON RoundNumber where
  parseJSON =
    A.withObject "RoundNumber" $
      \o ->
        do
          roundNumber <- o A..: "roundNumber"
          pure RoundNumber{..}

instance A.ToJSON RoundNumber where
  toJSON RoundNumber{..} =
    A.object ["roundNumber" A..= roundNumber]

deriving stock instance Generic v => Generic (Vote v)
deriving stock instance Ord v => Ord (Vote v)
deriving stock instance Read v => Read (Vote v)
deriving stock instance Show v => Show (Vote v)

instance A.FromJSON v => A.FromJSON (Vote v) where
  parseJSON =
    A.withObject "Block" $
      \o ->
        do
          votingRound <- o A..: "votingRound"
          creatorId <- o A..: "creatorId"
          committeeMembershipProof <- o A..: "committeeMembershipProof"
          blockHash <- o A..: "blockHash"
          signature <- o A..: "signature"
          pure MkVote{..}

instance A.ToJSON v => A.ToJSON (Vote v) where
  toJSON MkVote{..} =
    A.object
      [ "votingRound" A..= votingRound
      , "creatorId" A..= creatorId
      , "committeeMembershipProof" A..= committeeMembershipProof
      , "blockHash" A..= blockHash
      , "signature" A..= signature
      ]

deriving stock instance Generic Chain
deriving stock instance Ord Chain
deriving stock instance Read Chain
deriving stock instance Show Chain

instance A.FromJSON Chain where
  parseJSON =
    A.withObject "Chain" $
      \o ->
        do
          blocks <- o A..: "blocks"
          votes <- o A..: "votes"
          pure MkChain{..}

instance A.ToJSON Chain where
  toJSON MkChain{..} =
    A.object
      [ "blocks" A..= blocks
      , "votes" A..= votes
      ]

deriving stock instance Generic Hash
deriving stock instance Ord Hash
deriving via Bytes instance Read Hash
deriving via Bytes instance Show Hash
deriving via Bytes instance IsString Hash
deriving via Bytes instance A.FromJSON Hash
deriving via Bytes instance A.ToJSON Hash

deriving stock instance Eq Message
deriving stock instance Generic Message
deriving stock instance Ord Message
deriving stock instance Read Message
deriving stock instance Show Message

instance A.FromJSON Message where
  parseJSON =
    A.withObject "Message" $
      \o ->
        do
          input <- o A..: "input"
          case input of
            "NextSlot" -> NextSlot <$> o A..: "slot"
            "SomeBlock" -> SomeBlock <$> o A..: "block"
            "NewChain" -> NewChain <$> o A..: "chain"
            _ -> A.parseFail $ "Illegal input: " <> input

instance A.ToJSON Message where
  toJSON (NextSlot slot) =
    A.object
      [ "input" A..= ("NextSlot" :: String)
      , "slot" A..= slot
      ]
  toJSON (SomeBlock block) =
    A.object
      [ "input" A..= ("SomeBlock" :: String)
      , "block" A..= block
      ]
  toJSON (NewChain chain) =
    A.object
      [ "input" A..= ("NewChain" :: String)
      , "chain" A..= chain
      ]

deriving stock instance Generic LeadershipProof
deriving stock instance Ord LeadershipProof
deriving via Bytes instance Read LeadershipProof
deriving via Bytes instance Show LeadershipProof
deriving via Bytes instance IsString LeadershipProof
deriving via Bytes instance A.FromJSON LeadershipProof
deriving via Bytes instance A.ToJSON LeadershipProof

deriving stock instance Generic MembershipProof
deriving stock instance Ord MembershipProof
deriving via Bytes instance Read MembershipProof
deriving via Bytes instance Show MembershipProof
deriving via Bytes instance IsString MembershipProof
deriving via Bytes instance A.FromJSON MembershipProof
deriving via Bytes instance A.ToJSON MembershipProof

deriving stock instance Eq NodeId
deriving stock instance Generic NodeId
deriving stock instance Ord NodeId

instance Read NodeId where
  readsPrec _ = pure . (,"") . MkNodeId

instance Show NodeId where
  show = nodeId

instance IsString NodeId where
  fromString = MkNodeId

instance A.FromJSON NodeId where
  parseJSON = A.withText "NodeId" $ pure . MkNodeId . T.unpack

instance A.ToJSON NodeId where
  toJSON = A.String . T.pack . nodeId

instance A.FromJSONKey NodeId where
  fromJSONKey = A.FromJSONKeyTextParser $ pure . MkNodeId . T.unpack

instance A.ToJSONKey NodeId where
  toJSONKey = A.toJSONKeyText $ T.pack . nodeId

deriving stock instance Generic Signature
deriving stock instance Ord Signature
deriving via Bytes instance Read Signature
deriving via Bytes instance Show Signature
deriving via Bytes instance IsString Signature
deriving via Bytes instance A.FromJSON Signature
deriving via Bytes instance A.ToJSON Signature

deriving stock instance Generic VerificationKey
deriving stock instance Ord VerificationKey
deriving via Bytes instance Read VerificationKey
deriving via Bytes instance Show VerificationKey
deriving via Bytes instance IsString VerificationKey
deriving via Bytes instance A.FromJSON VerificationKey
deriving via Bytes instance A.ToJSON VerificationKey
