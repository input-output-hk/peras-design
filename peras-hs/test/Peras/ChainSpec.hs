{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Peras.ChainSpec where

import Data.Data (Proxy (..))
import Peras.Arbitraries ()
import Peras.Block (Block (..), PartyId, Slot, Tx)
import Peras.Chain (Chain (..), asChain, asList, commonPrefix, prefix)
import Peras.Crypto (Hash, LeadershipProof, MembershipProof)
import Peras.Orphans ()
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (..), Property, forAll, forAllShrink, (===), (==>))
import Test.QuickCheck.Classes (lawsCheck, showReadLaws)
import Test.QuickCheck.Property (once)

spec :: Spec
spec = do
  describe "Read/Show instances" $ do
    it "can read a simple Chain" $ do
      let v = read @(Chain ()) "Cons (Block {slotNumber = 1, creatorId = \"00010000\", parentBlock = \"00000000\", includedVotes = (), leadershipProof = \"01000101\", payload = [], signature = \"00000100\"}) Genesis"
      v `shouldBe` Cons (Block{slotNumber = 1, creatorId = "00010000", parentBlock = "00000000", includedVotes = (), leadershipProof = "01000101", payload = [], signature = "00000100"}) Genesis
    prop "read is inverse to show: Chain ()" $ lawsCheck $ showReadLaws (Proxy @(Chain ()))
    prop "read is inverse to show: PartyId" $ lawsCheck $ showReadLaws (Proxy @PartyId)
    prop "read is inverse to show: Slot" $ lawsCheck $ showReadLaws (Proxy @Slot)
    prop "read is inverse to show: Hash" $ lawsCheck $ showReadLaws (Proxy @Hash)
    prop "read is inverse to show: LeadershipProof" $ lawsCheck $ showReadLaws (Proxy @LeadershipProof)
    prop "read is inverse to show: MembershipProof" $ lawsCheck $ showReadLaws (Proxy @MembershipProof)
    prop "read is inverse to show: Tx" $ lawsCheck $ showReadLaws (Proxy @Tx)
  describe "Common Prefix" $ do
    prop "asChain is inverse to asList" propAsChainInverseAsList
    prop "selfPrefix: (c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)" propCommonPrefixSelf
    prop "prefixExtended : (c : Chain) -> (b1, b2 : Block) -> (commonPrefix (Cons b1 c ∷ Cons b2  c ∷ []) ≡ c)" propCommonPrefixExtended
    prop "Sample chain" $
      once $
        commonPrefix sampleChains === Cons (Block{slotNumber = 44, creatorId = "ece20dec9edc", parentBlock = "", includedVotes = (), leadershipProof = "0faf57e3c126", payload = [], signature = "c63cff5266ee"}) Genesis

sampleChains =
  [ chain1
  , chain2
  , chain1
  , chain1
  , chain1
  , chain2
  , chain1
  , chain1
  , chain1
  , chain1
  ]

chain1 = Cons (Block{slotNumber = 49, creatorId = "7392b2bd2853", parentBlock = "", includedVotes = (), leadershipProof = "f2a6ab5f8122", payload = [], signature = "06f34b7da9fd"}) (Cons (Block{slotNumber = 44, creatorId = "ece20dec9edc", parentBlock = "", includedVotes = (), leadershipProof = "0faf57e3c126", payload = [], signature = "c63cff5266ee"}) Genesis)

chain2 = Cons (Block{slotNumber = 44, creatorId = "ece20dec9edc", parentBlock = "", includedVotes = (), leadershipProof = "0faf57e3c126", payload = [], signature = "c63cff5266ee"}) Genesis

propAsChainInverseAsList :: Chain () -> Property
propAsChainInverseAsList c =
  let blocks = asList c
   in asChain blocks === c

propCommonPrefixSelf :: Property
propCommonPrefixSelf =
  forAllShrink arbitrary shrink $ \c ->
    commonPrefix @() [c, c] === c

propCommonPrefixExtended :: Chain () -> Block () -> Block () -> Property
propCommonPrefixExtended c b1 b2 =
  b1 /= b2 ==> commonPrefix [Cons b1 c, Cons b2 c] === c
