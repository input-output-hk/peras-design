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

module MAlonzo.Code.Haskell.Law.Functor.Def where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Prim.Functor
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

-- Haskell.Law.Functor.Def.IsLawfulFunctor
d_IsLawfulFunctor_12 a0 a1 = ()
data T_IsLawfulFunctor_12 = C_IsLawfulFunctor'46'constructor_3685

-- Haskell.Law.Functor.Def.IsLawfulFunctor.identity
d_identity_32 ::
  T_IsLawfulFunctor_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity_32 = erased

-- Haskell.Law.Functor.Def.IsLawfulFunctor.composition
d_composition_40 ::
  T_IsLawfulFunctor_12 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composition_40 = erased

-- Haskell.Law.Functor.Def._.composition
d_composition_44 ::
  T_IsLawfulFunctor_12 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composition_44 = erased

-- Haskell.Law.Functor.Def._.identity
d_identity_46 ::
  T_IsLawfulFunctor_12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity_46 = erased

-- Haskell.Law.Functor.Def.iLawfulFunctorFun
d_iLawfulFunctorFun_50 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Functor.Def.iLawfulFunctorFun"

-- Haskell.Law.Functor.Def.iLawfulFunctorTuple₂
d_iLawfulFunctorTuple'8322'_54 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Functor.Def.iLawfulFunctorTuple\8322"

-- Haskell.Law.Functor.Def.iLawfulFunctorTuple₃
d_iLawfulFunctorTuple'8323'_58 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Haskell.Law.Functor.Def.iLawfulFunctorTuple\8323"
