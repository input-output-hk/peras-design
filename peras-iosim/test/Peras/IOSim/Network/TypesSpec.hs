{-# LANGUAGE TypeApplications #-}

module Peras.IOSim.Network.TypesSpec where

import Paths_peras_iosim (getDataDir)
import Peras.IOSim.Network.Types (Topology)
import Test.Aeson.GenericSpecs (
  GoldenDirectoryOption (..),
  Proxy (Proxy),
  Settings (..),
  defaultSettings,
  roundtripAndGoldenSpecsWithSettings,
 )
import Test.Hspec (Spec, runIO)

spec :: Spec
spec =
  do
    goldenDir <- runIO getDataDir
    let settings = defaultSettings{goldenDirectoryOption = CustomDirectoryName goldenDir}
    roundtripAndGoldenSpecsWithSettings settings (Proxy @Topology)
