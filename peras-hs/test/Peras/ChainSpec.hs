{-# LANGUAGE TypeApplications #-}

module Peras.ChainSpec where

import Peras.Arbitraries ()
import Peras.Chain (Chain, asChain, asList, commonPrefix)
import Peras.Orphans ()
import Test.Hspec (Spec)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (..), Property, forAllShrink, (===))

spec :: Spec
spec = do
  prop "asChain is inverse to asList" propAsChainInverseAsList
  prop "(c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)" propCommonPrefixSelf

propAsChainInverseAsList :: Chain () -> Property
propAsChainInverseAsList c =
  let blocks = asList c
   in asChain blocks === c

propCommonPrefixSelf :: Property
propCommonPrefixSelf =
  forAllShrink arbitrary shrink $ \c ->
    commonPrefix @() [c, c] === c
