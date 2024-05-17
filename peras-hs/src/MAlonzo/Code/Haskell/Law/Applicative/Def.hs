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

module MAlonzo.Code.Haskell.Law.Applicative.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Law.Functor.Def
import qualified MAlonzo.Code.Haskell.Prim.Applicative
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

-- Haskell.Law.Applicative.Def.IsLawfulApplicative
d_IsLawfulApplicative_12 a0 a1 = ()
data T_IsLawfulApplicative_12
  = C_IsLawfulApplicative'46'constructor_12561

-- Haskell.Law.Applicative.Def.IsLawfulApplicative.super
d_super_66 ::
  T_IsLawfulApplicative_12 ->
  MAlonzo.Code.Haskell.Law.Functor.Def.T_IsLawfulFunctor_12
d_super_66 = erased

-- Haskell.Law.Applicative.Def.IsLawfulApplicative.identity
d_identity_70 ::
  T_IsLawfulApplicative_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity_70 = erased

-- Haskell.Law.Applicative.Def.IsLawfulApplicative.composition
d_composition_84 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composition_84 = erased

-- Haskell.Law.Applicative.Def.IsLawfulApplicative.homomorphism
d_homomorphism_94 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_homomorphism_94 = erased

-- Haskell.Law.Applicative.Def.IsLawfulApplicative.interchange
d_interchange_106 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interchange_106 = erased

-- Haskell.Law.Applicative.Def.IsLawfulApplicative.functor
d_functor_112 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_functor_112 = erased

-- Haskell.Law.Applicative.Def._.composition
d_composition_116 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composition_116 = erased

-- Haskell.Law.Applicative.Def._.functor
d_functor_118 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_functor_118 = erased

-- Haskell.Law.Applicative.Def._.homomorphism
d_homomorphism_120 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_homomorphism_120 = erased

-- Haskell.Law.Applicative.Def._.identity
d_identity_122 ::
  T_IsLawfulApplicative_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity_122 = erased

-- Haskell.Law.Applicative.Def._.interchange
d_interchange_124 ::
  T_IsLawfulApplicative_12 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interchange_124 = erased

-- Haskell.Law.Applicative.Def._.super
d_super_126 ::
  T_IsLawfulApplicative_12 ->
  MAlonzo.Code.Haskell.Law.Functor.Def.T_IsLawfulFunctor_12
d_super_126 = erased

-- Haskell.Law.Applicative.Def.iLawfulApplicativeFun
d_iLawfulApplicativeFun_130 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Applicative.Def.iLawfulApplicativeFun"

-- Haskell.Law.Applicative.Def.iLawfulApplicativeTuple₂
d_iLawfulApplicativeTuple'8322'_134 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Applicative.Def.iLawfulApplicativeTuple\8322"

-- Haskell.Law.Applicative.Def.iLawfulApplicativeTuple₃
d_iLawfulApplicativeTuple'8323'_138 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Applicative.Def.iLawfulApplicativeTuple\8323"
