{-# LANGUAGE OverloadedStrings #-}

module Peras.NodeSpec where

import qualified Data.ByteString as BS
import Foreign (newArray, peekArray)
import Peras.Node (ByteBuffer (..), receiveFfi, sendFfi)
import Test.Hspec (Spec, it, shouldBe, shouldReturn)

spec :: Spec
spec =
  it "can receive sent data" $ do
    dataBytes <- newArray (BS.unpack "1234567890")

    let buffer = ByteBuffer 10 dataBytes
    sendFfi 123 buffer `shouldReturn` True

    res <- receiveFfi
    case res of
      Left err -> fail err
      Right (buffer', addr) -> do
        addr `shouldBe` 123
        bufferSize buffer' `shouldBe` 10
        (BS.pack <$> peekArray 10 (bytes buffer')) `shouldReturn` "1234567890"
