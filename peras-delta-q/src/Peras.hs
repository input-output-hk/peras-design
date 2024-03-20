-- | ΔQ models for Praos and Peras.
module Peras where

import A (A (..))
import Data.List.NonEmpty (fromList)
import Data.Ratio ((%))
import DeltaQ.QTA (fromQTA)
import OBox (O (..), Tag (..), alt, box, (=>=))
import Reals (Rops)
import qualified Reals
import UnitInterval (Iops)
import qualified UnitInterval

singleMTURoundtrip :: (Rops r, Iops i) => A r i
singleMTURoundtrip =
  fromQTA $
    fromList [(oneThird, toR 0.012), (oneThird, toR 0.069), (oneThird, toR 0.268)]

payload64KRoundtrip :: (Rops r, Iops i) => A r i
payload64KRoundtrip =
  fromQTA $
    fromList [(oneThird, toR 0.024), (oneThird, toR 0.143), (oneThird, toR 0.531)]

headerBodyDiffusion :: (Rops r, Iops i) => A r i
headerBodyDiffusion =
  singleMTURoundtrip `Conv` singleMTURoundtrip -- `Conv` singleMTURoundtrip `Conv` payload64KRoundtrip

multihopsDiffusion :: (Rops r, Iops i) => Int -> A r i -> A r i
multihopsDiffusion n base =
  foldl Conv base $ replicate (n - 1) base

toI :: Iops i => Double -> i
toI = UnitInterval.fromDouble

toR :: Rops r => Double -> r
toR = Reals.fromDouble

oneThird :: Iops i => i
oneThird = toI $ fromRational $ 1 % 3

fullPraos :: O
fullPraos =
  let
    oneHop =
      Annotated
        (Tag "1 hop" "1 hop")
        ( box
            "req hdr"
            =>= box "rep hdr"
            =>= box "req body"
            =>= box "rep body"
        )
    twoHops =
      alt
        1
        oneHop
        ( alt
            5
            (Annotated (Tag "2 hops" "2 hops") $ oneHop =>= oneHop)
            ( alt
                36
                (Annotated (Tag "3 hops" "3 hops") $ oneHop =>= oneHop =>= oneHop)
                ( alt
                    98
                    (Annotated (Tag "4 hops" "4 hops") $ oneHop =>= oneHop =>= oneHop =>= oneHop)
                    (Annotated (Tag "5 hops" "5 hops") $ oneHop =>= oneHop =>= oneHop =>= oneHop =>= oneHop)
                )
            )
        )
   in
    twoHops
