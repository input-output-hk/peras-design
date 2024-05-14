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

module MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
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

-- Relation.Binary.PropositionalEquality.Algebra.isMagma
d_isMagma_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_14 ~v0 ~v1 ~v2 = du_isMagma_14
du_isMagma_14 :: MAlonzo.Code.Algebra.Structures.T_IsMagma_144
du_isMagma_14 =
  coe
    MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_785
    ( coe
        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396
    )
    erased

-- Relation.Binary.PropositionalEquality.Algebra.magma
d_magma_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_8
d_magma_20 ~v0 ~v1 v2 = du_magma_20 v2
du_magma_20 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_8
du_magma_20 v0 =
  coe
    MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_193
    v0
    (coe du_isMagma_14)
