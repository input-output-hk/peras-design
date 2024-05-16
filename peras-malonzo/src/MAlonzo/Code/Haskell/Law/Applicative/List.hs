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

module MAlonzo.Code.Haskell.Law.Applicative.List where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Haskell.Law.Applicative.Def
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

-- Haskell.Law.Applicative.List.identityList
d_identityList_12 ::
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identityList_12 = erased

-- Haskell.Law.Applicative.List.compositionList
d_compositionList_34 ::
  () ->
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compositionList_34 = erased

-- Haskell.Law.Applicative.List.interchangeList
d_interchangeList_52 ::
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interchangeList_52 = erased

-- Haskell.Law.Applicative.List.functorList
d_functorList_72 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_functorList_72 = erased

-- Haskell.Law.Applicative.List.iLawfulApplicativeList
d_iLawfulApplicativeList_92 ::
  MAlonzo.Code.Haskell.Law.Applicative.Def.T_IsLawfulApplicative_12
d_iLawfulApplicativeList_92 = erased
