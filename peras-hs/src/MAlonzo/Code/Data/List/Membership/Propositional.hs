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

module MAlonzo.Code.Data.List.Membership.Propositional where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Membership.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
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

-- Data.List.Membership.Propositional._._∈_
d__'8712'__14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  ()
d__'8712'__14 = erased

-- Data.List.Membership.Propositional._._∉_
d__'8713'__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  ()
d__'8713'__16 = erased

-- Data.List.Membership.Propositional._._∷=_
d__'8759''61'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  [AgdaAny]
d__'8759''61'__18 ~v0 ~v1 = du__'8759''61'__18
du__'8759''61'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  [AgdaAny]
du__'8759''61'__18 =
  coe MAlonzo.Code.Data.List.Membership.Setoid.du__'8759''61'__50

-- Data.List.Membership.Propositional._._─_
d__'9472'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  [AgdaAny]
d__'9472'__20 ~v0 ~v1 = du__'9472'__20
du__'9472'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  [AgdaAny]
du__'9472'__20 =
  coe MAlonzo.Code.Data.List.Membership.Setoid.du__'9472'__52

-- Data.List.Membership.Propositional._.find
d_find_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find_22 ~v0 ~v1 = du_find_22
du_find_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find_22 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Data.List.Membership.Setoid.du_find_84
    ( coe
        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
    )
    v2
    v3

-- Data.List.Membership.Propositional._.mapWith∈
d_mapWith'8712'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  ( AgdaAny ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    AgdaAny
  ) ->
  [AgdaAny]
d_mapWith'8712'_24 ~v0 ~v1 = du_mapWith'8712'_24
du_mapWith'8712'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  ( AgdaAny ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    AgdaAny
  ) ->
  [AgdaAny]
du_mapWith'8712'_24 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_62
    ( coe
        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
    )
    v2
    v3

-- Data.List.Membership.Propositional._≢∈_
d__'8802''8712'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  ()
d__'8802''8712'__32 = erased

-- Data.List.Membership.Propositional.lose
d_lose_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lose_50 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_lose_50 v4 v5
du_lose_50 ::
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_lose_50 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Membership.Setoid.du_lose_94
    (coe (\v2 v3 v4 v5 -> v5))
    (coe v0)
    (coe v1)
