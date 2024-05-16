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

module MAlonzo.Code.Haskell.Prim.Maybe where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
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

-- Haskell.Prim.Maybe.Maybe
d_Maybe_10 a0 a1 = ()
data T_Maybe_10 = C_Nothing_16 | C_Just_18 AgdaAny

-- Haskell.Prim.Maybe.maybe
d_maybe_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_Maybe_10 ->
  AgdaAny
d_maybe_28 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_maybe_28 v4 v5 v6
du_maybe_28 ::
  AgdaAny -> (AgdaAny -> AgdaAny) -> T_Maybe_10 -> AgdaAny
du_maybe_28 v0 v1 v2 =
  case coe v2 of
    C_Nothing_16 -> coe v0
    C_Just_18 v3 -> coe v1 v3
    _ -> MAlonzo.RTE.mazUnreachableError
