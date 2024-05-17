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

module MAlonzo.Code.Haskell.Prim.Either where

import qualified Data.Text
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

-- Haskell.Prim.Either.Either
d_Either_10 a0 a1 = ()
data T_Either_10 = C_Left_16 AgdaAny | C_Right_18 AgdaAny

-- Haskell.Prim.Either.either
d_either_20 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_Either_10 ->
  AgdaAny
d_either_20 ~v0 ~v1 ~v2 v3 v4 v5 = du_either_20 v3 v4 v5
du_either_20 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_Either_10 ->
  AgdaAny
du_either_20 v0 v1 v2 =
  case coe v2 of
    C_Left_16 v3 -> coe v0 v3
    C_Right_18 v3 -> coe v1 v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Haskell.Prim.Either.testBool
d_testBool_36 :: Bool -> T_Either_10
d_testBool_36 v0 =
  if coe v0 then coe C_Right_18 erased else coe C_Left_16 erased
