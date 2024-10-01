{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Peras.ChainSpec where

import Data.Data (Proxy (..))
import Peras.Arbitraries ()
import Peras.Block (Block (..), PartyId, Tx)
import Peras.Chain (Chain, commonPrefix)
import Peras.Crypto (Hash (..), LeadershipProof, MembershipProof)
import Peras.Numbering (SlotNumber)
import Peras.Orphans ()
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (..), Property, forAllShrink, (===), (==>))
import Test.QuickCheck.Classes (lawsCheck, showReadLaws)
import Test.QuickCheck.Property (once)

spec :: Spec
spec = do
  describe "Read/Show instances" $ do
    prop "read is inverse to show: Chain" $ lawsCheck $ showReadLaws (Proxy @Chain)
    prop "read is inverse to show: PartyId" $ lawsCheck $ showReadLaws (Proxy @PartyId)
    prop "read is inverse to show: Slot" $ lawsCheck $ showReadLaws (Proxy @SlotNumber)
    prop "read is inverse to show: Hash" $ lawsCheck $ showReadLaws (Proxy @(Hash ()))
    prop "read is inverse to show: LeadershipProof" $ lawsCheck $ showReadLaws (Proxy @LeadershipProof)
    prop "read is inverse to show: MembershipProof" $ lawsCheck $ showReadLaws (Proxy @MembershipProof)
    prop "read is inverse to show: Tx" $ lawsCheck $ showReadLaws (Proxy @Tx)
  describe "Common Prefix" $ do
    prop "selfPrefix: (c₁ ≡ c₂) -> (commonPrefix (c₁ ∷ c₂ ∷ []) ≡ c₁)" propCommonPrefixSelf
    prop "prefixExtended : (c : Chain) -> (b1, b2 : Block) -> (commonPrefix (Cons b1 c ∷ Cons b2  c ∷ []) ≡ c)" propCommonPrefixExtended
    prop "Sample chain" $
      once $
        commonPrefix sampleChains === [block2]

sampleChains :: [Chain]
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

block1 :: Block
block1 = MkBlock{slotNumber = 49, creatorId = 1, parentBlock = MkHash{hashBytes = ""}, certificate = Nothing, leadershipProof = "f2a6ab5f8122", bodyHash = MkHash{hashBytes = "12345678"}, signature = "06f34b7da9fd"}

block2 :: Block
block2 = MkBlock{slotNumber = 44, creatorId = 2, parentBlock = MkHash{hashBytes = ""}, certificate = Nothing, leadershipProof = "0faf57e3c126", bodyHash = MkHash{hashBytes = "12345678"}, signature = "c63cff5266ee"}

chain1 :: Chain
chain1 = [block1, block2]

chain2 :: Chain
chain2 = [block2]

propCommonPrefixSelf :: Property
propCommonPrefixSelf =
  forAllShrink arbitrary shrink $ \c ->
    commonPrefix [c, c] === c

propCommonPrefixExtended :: Chain -> Block -> Block -> Property
propCommonPrefixExtended c b1 b2 =
  b1 /= b2 ==> commonPrefix [b1 : c, b2 : c] === c
