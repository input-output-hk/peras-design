{-# LANGUAGE TypeApplications #-}

module Peras.OrphansSpec where

import Paths_peras_hs (getDataDir)
import Peras.Arbitraries ()
import Peras.Chain (Chain)
import Peras.Orphans ()
import Test.Aeson.GenericSpecs (GoldenDirectoryOption (..), Proxy (Proxy), Settings (..), defaultSettings, roundtripAndGoldenSpecsWithSettings)
import Test.Hspec (Spec, runIO)

spec :: Spec
spec =
  do
    goldenDir <- runIO getDataDir
    roundtripAndGoldenSpecsWithSettings
      (defaultSettings{goldenDirectoryOption = CustomDirectoryName goldenDir})
      (Proxy @Chain)
