module Peras.ALBASpec where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Function ((&))
import Data.Serialize (encode)
import Peras.ALBA (Hashable (..), Params (..), Proof (..), computeParams, modBS, prove, verify)
import Test.Hspec (Spec, SpecWith, describe, it)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (Gen, Positive (..), Property, Small (..), arbitrary, counterexample, forAll, resize, sized, vectorOf, (=/=), (===), (==>))
import Test.QuickCheck.Instances.ByteString ()

spec :: Spec
spec = do
  prop "can hash bytestrings" prop_hashBytestring
  prop "can take modulus of a bytestring" prop_modBytestring
  describe "parameters w/in expected bounds" $
    mapM_
      checkParameters
      [ (Params 128 128 600 400, 232)
      , (Params 128 128 660 330, 136)
      , (Params 128 128 800 200, 68)
      ]

  prop "can verify small proof is valid" $ prop_verifyValidProof 10
  modifyMaxSuccess (const 10) $
    prop "can verify large proof is valid" $
      prop_verifyValidProof 100

prop_verifyValidProof :: Integer -> Property
prop_verifyValidProof coeff =
  forAll (resize (fromInteger coeff) genItems) $ \items -> do
    let params = Params 8 8 (coeff * 8 `div` 10) (coeff * 2 `div` 10)
        (u, _, q) = computeParams params
        proof = prove params items
    verify params proof === True
      & counterexample ("u = " <> show u <> ", q = " <> show q <> ", proof = " <> show proof)

genItems :: Gen [ByteString]
genItems = sized $ \n -> vectorOf n (BS.pack <$> vectorOf 8 arbitrary)

checkParameters :: (Params, Integer) -> SpecWith ()
checkParameters (params, expected) =
  it ("check u = " <> show expected <> " for " <> show params) $
    let (u, _, _) = computeParams params
     in abs (u - expected) <= 3

prop_hashBytestring :: ByteString -> ByteString -> Property
prop_hashBytestring bytes1 bytes2 =
  bytes1 /= bytes2 ==> hash bytes1 =/= hash bytes2

prop_modBytestring :: Positive Integer -> Positive (Small Integer) -> Property
prop_modBytestring (Positive x) (Positive (Small y)) =
  modBS (encode x) y === x `mod` y
