module Main (main) where

import Test.Hspec
import Test.QuickCheck
import TestModelQC

main :: IO ()
main = hspec $ do
  describe "Testing the test demo protocol" $ do
    it "honest node implementation" $ property prop_honest
