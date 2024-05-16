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

module MAlonzo.Code.Agda.Builtin.Sigma where

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

-- Agda.Builtin.Sigma.Σ
d_Σ_14 a0 a1 a2 a3 = ()
data T_Σ_14 = C__'44'__32 AgdaAny AgdaAny

-- Agda.Builtin.Sigma.Σ.fst
d_fst_28 :: T_Σ_14 -> AgdaAny
d_fst_28 v0 =
  case coe v0 of
    C__'44'__32 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Agda.Builtin.Sigma.Σ.snd
d_snd_30 :: T_Σ_14 -> AgdaAny
d_snd_30 v0 =
  case coe v0 of
    C__'44'__32 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError
