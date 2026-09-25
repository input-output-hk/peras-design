module Peras.Prototype.FetchingSpec where

import Control.Concurrent.Class.MonadSTM (newTVarIO, readTVarIO)
import Control.Tracer (nullTracer)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Peras.Arbitraries (generateWith)
import Peras.Block (Block, Certificate (..))
import qualified Peras.Chain as Vote
import qualified Peras.Conformance.Model as Model
import Peras.Crypto (hash)
import Peras.Prototype.Crypto (mkParty)
import Peras.Prototype.Fetching (chainWeight, fetching)
import Peras.Prototype.Types (PerasParams (..), PerasState (..), genesisCert, initialPerasState)
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (arbitrary)

spec :: Spec
spec = do
  let block = arbitrary `generateWith` 42 :: Block
      otherBlock = arbitrary `generateWith` 43 :: Block
      cert = MkCertificate 1 (hash block) 7
      heavierCert = MkCertificate 2 (hash block) 19
      unrelatedCert = MkCertificate 3 (hash otherBlock) 100
  describe "Certificate weights" $ do
    it "counts blocks without certificates" $
      chainWeight Set.empty [block, otherBlock] `shouldBe` 2
    it "uses the largest weight once per certified block and ignores unrelated certificates" $ do
      let certs' = [cert, heavierCert, unrelatedCert, heavierCert]
      chainWeight (Set.fromList certs') [block] `shouldBe` 20
      Model.chainWeight certs' [block] `shouldBe` 20
    it "does not add a boost for a zero-weight certificate" $
      chainWeight (Set.singleton cert{weight = 0}) [block] `shouldBe` 1
    it "includes weight in certificate equality and ordering" $ do
      let changed = cert{weight = 19}
      (cert == changed) `shouldBe` False
      compare cert changed `shouldBe` LT
      Set.size (Set.fromList [cert, changed]) `shouldBe` 2
    it "uses the same zero-weight genesis in both models" $ do
      genesisCert `shouldBe` Model.genesisCert
      weight genesisCert `shouldBe` 0
    prop "prototype and conformance chain weights agree" $ \certs' blocks ->
      chainWeight (Set.fromList certs') blocks == fromIntegral (Model.chainWeight certs' blocks)
    mapM_ (checkParameter block) [0, 7, 23]

checkParameter :: Block -> Integer -> Spec
checkParameter block boost =
  it ("creates certificates using current B = " <> show boost) $ do
    let params = Model.testParams{perasB = boost, perasτ = 1}
        vote = (arbitrary `generateWith` 42){Vote.votingRound = 1, Vote.blockHash = hash block}
        expected = MkCertificate 1 (hash block) (fromIntegral boost)
        model = Model.initialModelState{Model.protocol = params, Model.allVotes = [vote]}
    Model.certsFromQuorum model `shouldBe` [expected]
    stateVar <- newTVarIO initialPerasState
    result <- fetching nullTracer params (mkParty 1 [] []) stateVar 1 [[block]] [vote]
    result `shouldBe` Right ()
    state <- readTVarIO stateVar
    Map.member expected (certs state) `shouldBe` True
    chainWeight (Map.keysSet (certs state)) [block] `shouldBe` 1 + boost
    -- A later parameter change must not reweight an existing certificate.
    result' <- fetching nullTracer params{perasB = boost + 100} (mkParty 1 [] []) stateVar 2 [] []
    result' `shouldBe` Right ()
    state' <- readTVarIO stateVar
    chainWeight (Map.keysSet (certs state')) [block] `shouldBe` 1 + boost
