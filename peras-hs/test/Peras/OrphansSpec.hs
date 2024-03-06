{-# LANGUAGE TypeApplications #-}

module Peras.OrphansSpec where

import Paths_peras_hs (getDataDir)
import Peras.Arbitraries ()
import Peras.Block (Block)
import Peras.Chain (Chain)
import Peras.Event (Event)
import Peras.Orphans ()
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
    roundtripAndGoldenSpecsWithSettings settings (Proxy @Chain)
    roundtripAndGoldenSpecsWithSettings settings (Proxy @Event)
