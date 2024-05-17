{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Haskell.Law.Semigroup.Maybe where

import qualified Data.Text
import qualified MAlonzo.Code.Haskell.Law.Semigroup.Def
import qualified MAlonzo.Code.Haskell.Prim.Monoid
import MAlonzo.RTE (
  AgdaAny,
  add64,
  addInt,
  coe,
  eq64,
  eqInt,
  erased,
  geqInt,
  lt64,
  ltInt,
  mul64,
  mulInt,
  quot64,
  quotInt,
  rem64,
  remInt,
  sub64,
  subInt,
  word64FromNat,
  word64ToNat,
 )
import qualified MAlonzo.RTE

-- Haskell.Law.Semigroup.Maybe.iLawfulSemigroupMaybe
d_iLawfulSemigroupMaybe_10 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Monoid.T_Semigroup_8 ->
  MAlonzo.Code.Haskell.Law.Semigroup.Def.T_IsLawfulSemigroup_12 ->
  MAlonzo.Code.Haskell.Law.Semigroup.Def.T_IsLawfulSemigroup_12
d_iLawfulSemigroupMaybe_10 = erased
