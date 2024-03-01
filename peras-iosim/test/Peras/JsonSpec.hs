{-# LANGUAGE TypeApplications #-}

module Peras.JsonSpec where

import Paths_peras_iosim (getDataDir)
import Peras.IOSim.Message.Types (InEnvelope, OutEnvelope)
import Test.Aeson.GenericSpecs (GoldenDirectoryOption (..), Proxy (Proxy), Settings (..), defaultSettings, roundtripAndGoldenSpecsWithSettings)
import Test.Hspec (Spec, runIO)

spec :: Spec
spec =
  do
    goldenDir <- runIO getDataDir
    let settings = defaultSettings{goldenDirectoryOption = CustomDirectoryName goldenDir}
    roundtripAndGoldenSpecsWithSettings settings (Proxy @InEnvelope)
    roundtripAndGoldenSpecsWithSettings settings (Proxy @OutEnvelope)
