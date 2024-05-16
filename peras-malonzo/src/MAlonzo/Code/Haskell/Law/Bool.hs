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

module MAlonzo.Code.Haskell.Law.Bool where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
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

-- Haskell.Law.Bool.&&-sym
d_'38''38''45'sym_10 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'sym_10 = erased

-- Haskell.Law.Bool.&&-semantics
d_'38''38''45'semantics_16 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'semantics_16 = erased

-- Haskell.Law.Bool.&&-leftAssoc
d_'38''38''45'leftAssoc_24 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'leftAssoc_24 = erased

-- Haskell.Law.Bool.&&-leftAssoc'
d_'38''38''45'leftAssoc''_32 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'leftAssoc''_32 = erased

-- Haskell.Law.Bool.&&-leftTrue
d_'38''38''45'leftTrue_46 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'leftTrue_46 = erased

-- Haskell.Law.Bool.&&-leftTrue'
d_'38''38''45'leftTrue''_54 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'leftTrue''_54 = erased

-- Haskell.Law.Bool.&&-rightTrue
d_'38''38''45'rightTrue_60 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'rightTrue_60 = erased

-- Haskell.Law.Bool.&&-rightTrue'
d_'38''38''45'rightTrue''_68 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'38''38''45'rightTrue''_68 = erased

-- Haskell.Law.Bool.||-excludedMiddle
d_'124''124''45'excludedMiddle_74 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'124''124''45'excludedMiddle_74 = erased

-- Haskell.Law.Bool.||-leftTrue
d_'124''124''45'leftTrue_80 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'124''124''45'leftTrue_80 = erased

-- Haskell.Law.Bool.||-rightTrue
d_'124''124''45'rightTrue_88 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'124''124''45'rightTrue_88 = erased

-- Haskell.Law.Bool.not-not
d_not'45'not_92 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'not_92 = erased

-- Haskell.Law.Bool.not-involution
d_not'45'involution_98 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'involution_98 = erased
