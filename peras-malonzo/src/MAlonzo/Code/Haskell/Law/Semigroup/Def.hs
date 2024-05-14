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

module MAlonzo.Code.Haskell.Law.Semigroup.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
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

-- Haskell.Law.Semigroup.Def.IsLawfulSemigroup
d_IsLawfulSemigroup_12 a0 a1 = ()
data T_IsLawfulSemigroup_12
  = C_IsLawfulSemigroup'46'constructor_521

-- Haskell.Law.Semigroup.Def.IsLawfulSemigroup.associativity
d_associativity_32 ::
  T_IsLawfulSemigroup_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_associativity_32 = erased

-- Haskell.Law.Semigroup.Def._.associativity
d_associativity_36 ::
  T_IsLawfulSemigroup_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_associativity_36 = erased

-- Haskell.Law.Semigroup.Def.iLawfulSemigroupFun
d_iLawfulSemigroupFun_40 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Semigroup.Def.iLawfulSemigroupFun"

-- Haskell.Law.Semigroup.Def.iLawfulSemigroupUnit
d_iLawfulSemigroupUnit_42 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Semigroup.Def.iLawfulSemigroupUnit"

-- Haskell.Law.Semigroup.Def.iLawfulSemigroupTuple₂
d_iLawfulSemigroupTuple'8322'_48 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Semigroup.Def.iLawfulSemigroupTuple\8322"

-- Haskell.Law.Semigroup.Def.iLawfulSemigroupTuple₃
d_iLawfulSemigroupTuple'8323'_56 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Semigroup.Def.iLawfulSemigroupTuple\8323"
