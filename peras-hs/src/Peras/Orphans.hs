{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Orphans where

import Data.Aeson (
  FromJSON (parseJSON),
  FromJSONKey,
  ToJSON (toJSON),
  ToJSONKey,
  Value (String),
  withText,
 )
import Data.Aeson.Types (parseFail)
import Data.String (IsString (..))
import GHC.Generics (Generic)
import Peras.Block (Block (..), Party (..))
import Peras.Chain (Chain (..), RoundNumber (..), Vote (..))
import Peras.Crypto (Hash (..), LeadershipProof (..), MembershipProof (..), Signature (..), VerificationKey (..))
import Peras.Message (Message (..), NodeId (..))
import Text.Read (Read (readPrec))

import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Text as T

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

instance FromJSON Bytes where
  parseJSON = withText "Base 16 Bytes" $ either parseFail (pure . Bytes) . B16.decode . BS8.pack . T.unpack

instance ToJSON Bytes where
  toJSON = String . T.pack . init . tail . show

deriving via Bytes instance FromJSON BS.ByteString
deriving via Bytes instance ToJSON BS.ByteString

-- Orphans for `Peras.Block`.

deriving stock instance Generic Party
deriving stock instance Ord Party
deriving stock instance Read Party
deriving stock instance Show Party
instance FromJSON Party
instance ToJSON Party
instance FromJSONKey Party
instance ToJSONKey Party

deriving stock instance Generic Block
deriving stock instance Ord Block
deriving stock instance Read Block
deriving stock instance Show Block
instance FromJSON Block
instance ToJSON Block
instance FromJSONKey Block
instance ToJSONKey Block

-- Orphans for `Peras.Chain`.

deriving stock instance Generic RoundNumber
deriving stock instance Ord RoundNumber
deriving stock instance Read RoundNumber
deriving stock instance Show RoundNumber
instance FromJSON RoundNumber
instance ToJSON RoundNumber

deriving stock instance Generic v => Generic (Vote v)
deriving stock instance Ord v => Ord (Vote v)
deriving stock instance Read v => Read (Vote v)
deriving stock instance Show v => Show (Vote v)
instance (Generic v, FromJSON v) => FromJSON (Vote v)
instance (Generic v, ToJSON v) => ToJSON (Vote v)

deriving stock instance Generic Chain
deriving stock instance Ord Chain
deriving stock instance Read Chain
deriving stock instance Show Chain
instance FromJSON Chain
instance ToJSON Chain

-- Orphans for `Peras.Crypto`.

deriving stock instance Generic Hash
deriving stock instance Ord Hash
deriving via Bytes instance Read Hash
deriving via Bytes instance Show Hash
deriving via Bytes instance IsString Hash
instance FromJSON Hash
instance ToJSON Hash

deriving stock instance Generic MembershipProof
deriving stock instance Ord MembershipProof
deriving via Bytes instance Read MembershipProof
deriving via Bytes instance Show MembershipProof
deriving via Bytes instance IsString MembershipProof
instance FromJSON MembershipProof
instance ToJSON MembershipProof

deriving stock instance Generic LeadershipProof
deriving stock instance Ord LeadershipProof
deriving via Bytes instance Read LeadershipProof
deriving via Bytes instance Show LeadershipProof
deriving via Bytes instance IsString LeadershipProof
instance FromJSON LeadershipProof
instance ToJSON LeadershipProof

deriving stock instance Generic Signature
deriving stock instance Ord Signature
deriving via Bytes instance Read Signature
deriving via Bytes instance Show Signature
deriving via Bytes instance IsString Signature
instance FromJSON Signature
instance ToJSON Signature

deriving stock instance Generic VerificationKey
deriving stock instance Ord VerificationKey
deriving via Bytes instance Read VerificationKey
deriving via Bytes instance Show VerificationKey
deriving via Bytes instance IsString VerificationKey
instance FromJSON VerificationKey
instance ToJSON VerificationKey

-- Orphans for `Peras.Message`.

deriving stock instance Eq NodeId
deriving stock instance Generic NodeId
deriving stock instance Ord NodeId
deriving stock instance Read NodeId
deriving stock instance Show NodeId
instance IsString NodeId where
  fromString = MkNodeId

instance FromJSON NodeId
instance ToJSON NodeId
instance FromJSONKey NodeId
instance ToJSONKey NodeId

deriving stock instance Eq a => Eq (Message a)
deriving stock instance Generic a => Generic (Message a)
deriving stock instance Ord a => Ord (Message a)
deriving stock instance Read a => Read (Message a)
deriving stock instance Show a => Show (Message a)
instance (Generic a, FromJSON a) => FromJSON (Message a)
instance (Generic a, ToJSON a) => ToJSON (Message a)
