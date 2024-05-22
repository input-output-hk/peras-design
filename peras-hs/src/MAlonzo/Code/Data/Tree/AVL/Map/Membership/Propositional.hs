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

module MAlonzo.Code.Data.Tree.AVL.Map.Membership.Propositional where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Relation.Binary.Bundles
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

-- Data.Tree.AVL.Map.Membership.Propositional._.Map
d_Map_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ()
d_Map_194 = erased

-- Data.Tree.AVL.Map.Membership.Propositional._≈ₖᵥ_
d__'8776''8342''7525'__302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ()
d__'8776''8342''7525'__302 = erased

-- Data.Tree.AVL.Map.Membership.Propositional._∈ₖᵥ_
d__'8712''8342''7525'__304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ()
d__'8712''8342''7525'__304 = erased

-- Data.Tree.AVL.Map.Membership.Propositional._∉ₖᵥ_
d__'8713''8342''7525'__310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ()
d__'8713''8342''7525'__310 = erased
