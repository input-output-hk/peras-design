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

module MAlonzo.Code.Data.Unit.Polymorphic.Base where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
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

-- Data.Unit.Polymorphic.Base.⊤
d_'8868'_10 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_'8868'_10 = erased

-- Data.Unit.Polymorphic.Base.tt
d_tt_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Level.T_Lift_8
d_tt_16 ~v0 = du_tt_16
du_tt_16 :: MAlonzo.Code.Level.T_Lift_8
du_tt_16 =
  coe
    MAlonzo.Code.Level.C_lift_20
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)