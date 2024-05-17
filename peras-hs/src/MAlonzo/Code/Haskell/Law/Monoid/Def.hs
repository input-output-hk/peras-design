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

module MAlonzo.Code.Haskell.Law.Monoid.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
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

-- Haskell.Law.Monoid.Def.IsLawfulMonoid
d_IsLawfulMonoid_12 a0 a1 = ()
data T_IsLawfulMonoid_12 = C_IsLawfulMonoid'46'constructor_1345

-- Haskell.Law.Monoid.Def.IsLawfulMonoid.super
d_super_32 ::
  T_IsLawfulMonoid_12 ->
  MAlonzo.Code.Haskell.Law.Semigroup.Def.T_IsLawfulSemigroup_12
d_super_32 = erased

-- Haskell.Law.Monoid.Def.IsLawfulMonoid.rightIdentity
d_rightIdentity_36 ::
  T_IsLawfulMonoid_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightIdentity_36 = erased

-- Haskell.Law.Monoid.Def.IsLawfulMonoid.leftIdentity
d_leftIdentity_40 ::
  T_IsLawfulMonoid_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftIdentity_40 = erased

-- Haskell.Law.Monoid.Def.IsLawfulMonoid.concatenation
d_concatenation_44 ::
  T_IsLawfulMonoid_12 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concatenation_44 = erased

-- Haskell.Law.Monoid.Def._.concatenation
d_concatenation_48 ::
  T_IsLawfulMonoid_12 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concatenation_48 = erased

-- Haskell.Law.Monoid.Def._.leftIdentity
d_leftIdentity_50 ::
  T_IsLawfulMonoid_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftIdentity_50 = erased

-- Haskell.Law.Monoid.Def._.rightIdentity
d_rightIdentity_52 ::
  T_IsLawfulMonoid_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightIdentity_52 = erased

-- Haskell.Law.Monoid.Def._.super
d_super_54 ::
  T_IsLawfulMonoid_12 ->
  MAlonzo.Code.Haskell.Law.Semigroup.Def.T_IsLawfulSemigroup_12
d_super_54 = erased

-- Haskell.Law.Monoid.Def.iLawfulMonoidFun
d_iLawfulMonoidFun_58 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monoid.Def.iLawfulMonoidFun"

-- Haskell.Law.Monoid.Def.iLawfulMonoidUnit
d_iLawfulMonoidUnit_60 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monoid.Def.iLawfulMonoidUnit"

-- Haskell.Law.Monoid.Def.iLawfulMonoidTuple₂
d_iLawfulMonoidTuple'8322'_66 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monoid.Def.iLawfulMonoidTuple\8322"

-- Haskell.Law.Monoid.Def.iLawfulMonoidTuple₃
d_iLawfulMonoidTuple'8323'_74 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Monoid.Def.iLawfulMonoidTuple\8323"
