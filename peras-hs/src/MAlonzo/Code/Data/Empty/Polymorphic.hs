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

module MAlonzo.Code.Data.Empty.Polymorphic where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Level
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

-- Data.Empty.Polymorphic.⊥
d_'8869'_8 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_'8869'_8 = erased

-- Data.Empty.Polymorphic.⊥-elim
d_'8869''45'elim_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Level.T_Lift_8 -> ()) ->
  MAlonzo.Code.Level.T_Lift_8 ->
  AgdaAny
d_'8869''45'elim_20 ~v0 ~v1 ~v2 ~v3 = du_'8869''45'elim_20
du_'8869''45'elim_20 :: AgdaAny
du_'8869''45'elim_20 = MAlonzo.RTE.mazUnreachableError
