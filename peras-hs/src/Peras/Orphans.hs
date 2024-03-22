{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Orphans where

import Data.Aeson (
  FromJSON (parseJSON),
  FromJSONKey (..),
  FromJSONKeyFunction (FromJSONKeyTextParser),
  ToJSON (toJSON),
  ToJSONKey (..),
  Value (String),
  withText,
 )
import Data.Aeson.Types (parseFail, toJSONKeyText)
import Data.Bifunctor (bimap)
import Data.String (IsString (..))
import GHC.Generics (Generic)
import Peras.Block (Block (..), BlockBody (..), Certificate (..), Party (..))
import Peras.Chain (RoundNumber (..), Vote (..))
import Peras.Crypto (Hash (..), LeadershipProof (..), MembershipProof (..), Signature (..), VerificationKey (..))
import Peras.Event (Event (..), Rollback (..), UniqueId (..))
import Peras.Message (Message (..), NodeId (..))
import Text.Read (Read (readPrec))

import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Hashable as H (Hashable (..))
import qualified Data.Text as T

-- Only used for deriving instances of similar types.

newtype Bytes = Bytes {getBytes :: BS.ByteString}
  deriving (Eq, Generic, Ord)

instance Read Bytes where
  readPrec = do
    Right bs' <- B16.decode . BS8.pack <$> readPrec
    pure $ Bytes bs'

instance Show Bytes where
  show = show . BS8.unpack . B16.encode . getBytes

instance IsString Bytes where
  fromString = either error Bytes . B16.decode . BS8.pack

instance H.Hashable Bytes

instance FromJSON Bytes where
  parseJSON = withText "Base 16 Bytes" $ either parseFail (pure . Bytes) . B16.decode . BS8.pack . T.unpack

instance ToJSON Bytes where
  toJSON = String . T.pack . init . tail . show

instance FromJSONKey Bytes where
  fromJSONKey = FromJSONKeyTextParser $ \t ->
    case B16.decode . BS8.pack . T.unpack $ t of
      Left err -> fail err
      Right k -> pure $ Bytes k

instance ToJSONKey Bytes where
  toJSONKey = toJSONKeyText $ T.pack . init . tail . show

deriving via Bytes instance FromJSON BS.ByteString
deriving via Bytes instance ToJSON BS.ByteString

-- Orphans for `Peras.Block`.

deriving stock instance Generic Party
deriving stock instance Ord Party
deriving stock instance Read Party
deriving stock instance Show Party
deriving anyclass instance H.Hashable Party
instance FromJSON Party
instance ToJSON Party
instance FromJSONKey Party
instance ToJSONKey Party

deriving stock instance Generic Certificate
deriving stock instance Ord Certificate
deriving stock instance Read Certificate
deriving stock instance Show Certificate
instance H.Hashable Certificate
instance FromJSON Certificate
instance ToJSON Certificate

deriving stock instance Generic Block
deriving stock instance Ord Block
deriving stock instance Read Block
deriving stock instance Show Block
deriving anyclass instance H.Hashable Block
instance FromJSON Block
instance ToJSON Block

deriving stock instance Generic BlockBody
deriving stock instance Ord BlockBody
deriving stock instance Read BlockBody
deriving stock instance Show BlockBody
deriving anyclass instance H.Hashable BlockBody
instance FromJSON BlockBody
instance ToJSON BlockBody

-- Orphans for `Peras.Chain`.

deriving stock instance Generic RoundNumber
deriving stock instance Ord RoundNumber
deriving stock instance Read RoundNumber
deriving stock instance Show RoundNumber
deriving anyclass instance H.Hashable RoundNumber
deriving newtype instance FromJSON RoundNumber
deriving newtype instance ToJSON RoundNumber
deriving newtype instance FromJSONKey RoundNumber
deriving newtype instance ToJSONKey RoundNumber

instance Enum RoundNumber where
  toEnum = MkRoundNumber . toEnum
  fromEnum (MkRoundNumber i) = fromEnum i
instance Integral RoundNumber where
  MkRoundNumber i `quotRem` MkRoundNumber j = bimap MkRoundNumber MkRoundNumber $ i `quotRem` j
  toInteger (MkRoundNumber i) = toInteger i
instance Num RoundNumber where
  MkRoundNumber i + MkRoundNumber j = MkRoundNumber $ i + j
  MkRoundNumber i - MkRoundNumber j = MkRoundNumber $ i - j
  MkRoundNumber i * MkRoundNumber j = MkRoundNumber $ i * j
  abs (MkRoundNumber i) = MkRoundNumber $ abs i
  signum (MkRoundNumber i) = MkRoundNumber $ signum i
  fromInteger = MkRoundNumber . fromInteger
instance Real RoundNumber where
  toRational (MkRoundNumber i) = toRational i

deriving stock instance Generic Vote
deriving stock instance Ord Vote
deriving stock instance Read Vote
deriving stock instance Show Vote
deriving anyclass instance H.Hashable Vote
instance FromJSON Vote
instance ToJSON Vote

-- Orphans for `Peras.Crypto`.

deriving stock instance Generic a => Generic (Hash a)
deriving stock instance Ord a => Ord (Hash a)
deriving via Bytes instance Read a => Read (Hash a)
deriving via Bytes instance Show a => Show (Hash a)
deriving via Bytes instance IsString a => IsString (Hash a)
deriving via Bytes instance FromJSON a => FromJSON (Hash a)
deriving via Bytes instance ToJSON a => ToJSON (Hash a)

instance FromJSON a => FromJSONKey (Hash a) where
  fromJSONKey = FromJSONKeyTextParser $ \t ->
    case B16.decode . BS8.pack . T.unpack $ t of
      Left err -> fail err
      Right k -> pure $ Hash k

instance ToJSON a => ToJSONKey (Hash a) where
  toJSONKey = toJSONKeyText $ T.pack . init . tail . show . hashBytes

instance H.Hashable (Hash a) where
  hash = H.hash . hashBytes
  hashWithSalt = (. hashBytes) . H.hashWithSalt

deriving stock instance Generic MembershipProof
deriving stock instance Ord MembershipProof
deriving anyclass instance H.Hashable MembershipProof
deriving via Bytes instance Read MembershipProof
deriving via Bytes instance Show MembershipProof
deriving via Bytes instance IsString MembershipProof
deriving via Bytes instance FromJSON MembershipProof
deriving via Bytes instance ToJSON MembershipProof

deriving stock instance Generic LeadershipProof
deriving stock instance Ord LeadershipProof
deriving anyclass instance H.Hashable LeadershipProof
deriving via Bytes instance Read LeadershipProof
deriving via Bytes instance Show LeadershipProof
deriving via Bytes instance IsString LeadershipProof
deriving via Bytes instance FromJSON LeadershipProof
deriving via Bytes instance ToJSON LeadershipProof

deriving stock instance Generic Signature
deriving stock instance Ord Signature
deriving anyclass instance H.Hashable Signature
deriving via Bytes instance Read Signature
deriving via Bytes instance Show Signature
deriving via Bytes instance IsString Signature
deriving via Bytes instance FromJSON Signature
deriving via Bytes instance ToJSON Signature

deriving stock instance Generic VerificationKey
deriving stock instance Ord VerificationKey
deriving anyclass instance H.Hashable VerificationKey
deriving via Bytes instance Read VerificationKey
deriving via Bytes instance Show VerificationKey
deriving via Bytes instance IsString VerificationKey
deriving via Bytes instance FromJSON VerificationKey
deriving via Bytes instance ToJSON VerificationKey

-- Orphans for `Peras.Message`.

deriving stock instance Generic NodeId
instance IsString NodeId where
  fromString = MkNodeId

deriving newtype instance FromJSON NodeId
deriving newtype instance ToJSON NodeId
deriving newtype instance FromJSONKey NodeId
deriving newtype instance ToJSONKey NodeId
deriving newtype instance H.Hashable NodeId

deriving stock instance Eq Message
deriving stock instance Ord Message
deriving stock instance Generic Message
deriving instance Read Message
deriving instance Show Message
deriving anyclass instance H.Hashable Message
instance FromJSON Message
instance ToJSON Message

deriving stock instance Eq UniqueId
deriving stock instance Ord UniqueId
deriving via Bytes instance Read UniqueId
deriving via Bytes instance Show UniqueId
deriving via Bytes instance H.Hashable UniqueId
deriving via Bytes instance IsString UniqueId
deriving via Bytes instance FromJSON UniqueId
deriving via Bytes instance ToJSON UniqueId
deriving via Bytes instance FromJSONKey UniqueId
deriving via Bytes instance ToJSONKey UniqueId

-- Orphans for `Peras.Event`.

deriving stock instance Eq Event
deriving stock instance Generic Event
deriving stock instance Ord Event
deriving stock instance Read Event
deriving stock instance Show Event
deriving anyclass instance H.Hashable Event
instance FromJSON Event
instance ToJSON Event

deriving stock instance Eq Rollback
deriving stock instance Generic Rollback
deriving stock instance Ord Rollback
deriving stock instance Read Rollback
deriving stock instance Show Rollback
deriving anyclass instance H.Hashable Rollback
instance FromJSON Rollback
instance ToJSON Rollback
