module Peras.QCD.Crypto where

open import Haskell.Prelude

{-# FOREIGN AGDA2HS
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeSynonymInstances #-}
import qualified Data.Binary as B
import qualified Data.ByteString as BS (ByteString, concat, empty)
import qualified Data.ByteString.Lazy as LBS (toStrict)
import qualified Data.Hashable as H
import GHC.Generics (Generic)
type ByteString = BS.ByteString
#-}

{-# FOREIGN GHC
import qualified Data.Hashable as H
#-}

X = Int × Int × Int
{-# COMPILE AGDA2HS X #-}

-- Byte strings.

postulate
  ByteString : Set
  emptyBS : ByteString
  concatBS : List ByteString → ByteString
  eqBS : ByteString → ByteString → Bool
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC emptyBS = BS.empty #-}
{-# COMPILE GHC concatBS = BS.concat #-}
{-# COMPILE GHC eqBS = (==) #-}
{-# FOREIGN AGDA2HS
emptyBS :: ByteString
emptyBS = BS.empty
concatBS :: [ByteString] -> ByteString
concatBS = BS.concat
eqBS :: ByteString -> ByteString -> Bool
eqBS = (==)
#-}

-- Hashing.

record Hash (a : Set) : Set where
  constructor MakeHash
  field hashBytes : ByteString
open Hash public
{-# COMPILE AGDA2HS Hash newtype deriving (Generic, Show) #-}

instance
  iHashEq : Eq (Hash a)
  iHashEq ._==_ x y = eqBS (hashBytes x) (hashBytes y)
{-# COMPILE AGDA2HS iHashEq #-}

record Hashable (a : Set) : Set where
  field hash : a → Hash a
open Hashable public
{-# COMPILE AGDA2HS Hashable class #-}

postulate
  unsafeHash : a → ByteString
{-# COMPILE GHC unsafeHash = LBS.toStrict . B.encode . H.hash #-}
{-# FOREIGN AGDA2HS
unsafeHash :: H.Hashable a => a -> ByteString
unsafeHash = LBS.toStrict . B.encode . H.hash
#-}

instance
  iUnitHashable : Hashable ⊤
  iUnitHashable .hash _ = MakeHash $ unsafeHash tt
{-# COMPILE AGDA2HS iUnitHashable #-}

instance
  iByteStringHashable : Hashable ByteString
  iByteStringHashable .hash = MakeHash ∘ unsafeHash
{-# COMPILE AGDA2HS iByteStringHashable #-}

instance
  iHashHashable : Hashable (Hash a)
  iHashHashable .hash = (MakeHash ∘ unsafeHash) ∘ hashBytes
{-# COMPILE AGDA2HS iHashHashable #-}

instance
  iNatHashable : Hashable Nat
  iNatHashable .hash = MakeHash ∘ unsafeHash
{-# COMPILE AGDA2HS iNatHashable #-}

instance
  iListHashable : ⦃ i : Hashable a ⦄ → Hashable (List a)
  iListHashable {{i}} .hash = MakeHash ∘ unsafeHash ∘ concatBS ∘ fmap (λ x → hashBytes (hash i x))
{-# COMPILE AGDA2HS iListHashable #-}

instance
  iPairHashable : ⦃ i : Hashable a ⦄ → ⦃ j : Hashable b ⦄ → Hashable (a × b)
  iPairHashable {{i}} {{j}} .hash (x , y) =
    let
      hx = hashBytes (hash i x)
      hy = hashBytes (hash j y)
    in
      MakeHash $ unsafeHash (hx , hy)
{-# COMPILE AGDA2HS iPairHashable #-}

instance
  iTripletHashable : ⦃ i : Hashable a ⦄ → ⦃ j : Hashable b ⦄ → ⦃ k : Hashable c ⦄ → Hashable (a × b × c)
  iTripletHashable {{i}} {{j}} {{k}} .hash (x , y , z) =
    let
      hx = hashBytes (hash i x)
      hy = hashBytes (hash j y)
      hz = hashBytes (hash k z)
    in
      MakeHash $ unsafeHash (hx , hy , hz)
{-# COMPILE AGDA2HS iTripletHashable #-}

castHash : Hash a → Hash b
castHash = MakeHash ∘ hashBytes
{-# COMPILE AGDA2HS castHash #-}

instance
  iMaybeHashable : ⦃ i : Hashable a ⦄ → Hashable (Maybe a)
  iMaybeHashable {{_}} .hash Nothing = castHash (hash iUnitHashable tt)
  iMaybeHashable {{i}} .hash (Just x) = castHash (hash iPairHashable (tt , x))
{-# COMPILE AGDA2HS iMaybeHashable #-}