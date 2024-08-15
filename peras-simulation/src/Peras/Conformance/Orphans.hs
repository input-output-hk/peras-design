{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Peras.Conformance.Orphans () where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Peras.Conformance.Model (EnvAction (..), NodeModel (..))

deriving stock instance Generic EnvAction
instance FromJSON EnvAction
instance ToJSON EnvAction

deriving stock instance Generic NodeModel
instance FromJSON NodeModel
instance ToJSON NodeModel
