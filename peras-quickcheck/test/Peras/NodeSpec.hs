{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Peras.NodeSpec where

import qualified Data.ByteString as BS
import Foreign (peekArray)
import Peras.Node (ByteBuffer (..), receiveFfi, sendFfi)
import Test.Hspec (Spec, shouldBe, shouldReturn)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, arbitrary, forAll, listOf)
import Test.QuickCheck.Monadic (assert, monadicIO, run)

spec :: Spec
spec =
  prop "can receive sent data through dummy FFI" propDummyFFIReceivesOwnSends

newtype SomeBytes = SomeBytes {toSend :: BS.ByteString}
  deriving newtype (Eq, Show)

propDummyFFIReceivesOwnSends :: Property
propDummyFFIReceivesOwnSends =
  forAll genSomeBytes $ \SomeBytes{toSend} -> monadicIO $ do
    received <- run $ do
      let len = BS.length toSend

      sendFfi 123 toSend `shouldReturn` True
      res <- receiveFfi

      case res of
        Left err -> fail err
        Right (buffer', addr) -> do
          addr `shouldBe` 123
          bufferSize buffer' `shouldBe` fromIntegral len
          BS.pack <$> peekArray len (bytes buffer')

    assert $ received == toSend

genSomeBytes :: Gen SomeBytes
genSomeBytes = SomeBytes . BS.pack <$> listOf arbitrary
