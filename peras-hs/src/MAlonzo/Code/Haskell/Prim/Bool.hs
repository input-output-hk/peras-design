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

module MAlonzo.Code.Haskell.Prim.Bool where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
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

-- Haskell.Prim.Bool._&&_
d__'38''38'__6 :: Bool -> Bool -> Bool
d__'38''38'__6 v0 v1 = if coe v0 then coe v1 else coe v0

-- Haskell.Prim.Bool._||_
d__'124''124'__10 :: Bool -> Bool -> Bool
d__'124''124'__10 v0 v1 = if coe v0 then coe v0 else coe v1

-- Haskell.Prim.Bool.not
d_not_14 :: Bool -> Bool
d_not_14 v0 =
  if coe v0
    then coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
    else coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10

-- Haskell.Prim.Bool.otherwise
d_otherwise_16 :: Bool
d_otherwise_16 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
