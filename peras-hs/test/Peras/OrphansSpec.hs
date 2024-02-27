{-# LANGUAGE TypeApplications #-}

module Peras.OrphansSpec where

import Peras.Arbitraries ()
import Peras.Chain (Chain)
import Peras.Orphans ()
import Test.Aeson.GenericSpecs (Proxy (Proxy), roundtripAndGoldenSpecs)
import Test.Hspec (Spec)

spec :: Spec
spec =
  roundtripAndGoldenSpecs (Proxy @Chain)
