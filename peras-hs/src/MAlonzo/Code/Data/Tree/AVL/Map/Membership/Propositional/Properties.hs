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

module MAlonzo.Code.Data.Tree.AVL.Map.Membership.Propositional.Properties where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Product.Relation.Binary.Pointwise.NonDependent
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties
import qualified MAlonzo.Code.Data.Tree.AVL.Map
import qualified MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
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

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.Eq._≉_
d__'8777'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  ()
d__'8777'__72 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.Map
d_Map_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ()
d_Map_196 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.empty
d_empty_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_empty_200 ~v0 ~v1 ~v2 ~v3 = du_empty_200
du_empty_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_empty_200 v0 v1 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_198

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.insert
d_insert_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insert_210 ~v0 ~v1 ~v2 v3 = du_insert_210 v3
du_insert_210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_insert_210 v0 v1 v2 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202 (coe v0)

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.lookup
d_lookup_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  Maybe AgdaAny
d_lookup_222 ~v0 ~v1 ~v2 v3 = du_lookup_222 v3
du_lookup_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  Maybe AgdaAny
du_lookup_222 v0 v1 v2 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_208 (coe v0)

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.member
d_member_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Bool
d_member_226 ~v0 ~v1 ~v2 v3 = du_member_226 v3
du_member_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Bool
du_member_226 v0 v1 v2 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_member_214 (coe v0)

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.singleton
d_singleton_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_singleton_228 ~v0 ~v1 ~v2 ~v3 = du_singleton_228
du_singleton_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_singleton_228 v0 v1 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_singleton_200

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._._∈ₖᵥ_
d__'8712''8342''7525'__260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ()
d__'8712''8342''7525'__260 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._._∉ₖᵥ_
d__'8713''8342''7525'__262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ()
d__'8713''8342''7525'__262 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._._≈ₖᵥ_
d__'8776''8342''7525'__264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ()
d__'8776''8342''7525'__264 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.Any.Any
d_Any_268 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.Any.lookupKey
d_lookupKey_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  AgdaAny
d_lookupKey_274 ~v0 ~v1 ~v2 ~v3 = du_lookupKey_274
du_lookupKey_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  AgdaAny
du_lookupKey_274 v0 v1 v2 v3 v4 v5 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_lookupKey_348
    v4
    v5

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.≈ₖᵥ-trans
d_'8776''8342''7525''45'trans_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8776''8342''7525''45'trans_312 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 =
  du_'8776''8342''7525''45'trans_312 v3 v6 v7 v8
du_'8776''8342''7525''45'trans_312 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8776''8342''7525''45'trans_312 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Data.Product.Relation.Binary.Pointwise.NonDependent.du_'215''45'transitive_76
    ( let v4 =
            coe
              MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
              (coe v0)
       in coe
            ( let v5 =
                    coe
                      MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                      (coe v4)
               in coe
                    ( let v6 =
                            coe
                              MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                              (coe v5)
                       in coe
                            ( coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                ( coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v6)
                                )
                            )
                    )
            )
    )
    erased
    (coe v1)
    (coe v2)
    (coe v3)

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.≈ₖᵥ-sym
d_'8776''8342''7525''45'sym_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8776''8342''7525''45'sym_318 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 =
  du_'8776''8342''7525''45'sym_318 v3 v6 v7
du_'8776''8342''7525''45'sym_318 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8776''8342''7525''45'sym_318 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.Product.Relation.Binary.Pointwise.NonDependent.du_'215''45'symmetric_70
    ( let v3 =
            coe
              MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
              (coe v0)
       in coe
            ( let v4 =
                    coe
                      MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                      (coe v3)
               in coe
                    ( let v5 =
                            coe
                              MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                              (coe v4)
                       in coe
                            ( coe
                                MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                ( coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v5)
                                )
                            )
                    )
            )
    )
    erased
    (coe v1)
    (coe v2)

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-Respectsˡ
d_'8712''8342''7525''45'Respects'737'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'Respects'737'_324
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  v6
  v7
  v8
  v9 =
    du_'8712''8342''7525''45'Respects'737'_324 v3 v6 v7 v8 v9
du_'8712''8342''7525''45'Respects'737'_324 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
du_'8712''8342''7525''45'Respects'737'_324 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_map_338
    (coe v1)
    ( coe
        ( \v5 ->
            coe
              du_'8776''8342''7525''45'trans_312
              v0
              v3
              v2
              ( coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v5))
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v5))
              )
              (coe du_'8776''8342''7525''45'sym_318 v0 v2 v3 v4)
        )
    )

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-empty
d_'8712''8342''7525''45'empty_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8712''8342''7525''45'empty_328 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-singleton⁺
d_'8712''8342''7525''45'singleton'8314'_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'singleton'8314'_330
  ~v0
  ~v1
  ~v2
  v3
  v4
  ~v5
  ~v6
  v7 =
    du_'8712''8342''7525''45'singleton'8314'_330 v3 v4 v7
du_'8712''8342''7525''45'singleton'8314'_330 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
du_'8712''8342''7525''45'singleton'8314'_330 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336
    ( coe
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_singleton'8314'_1432
        ( coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            ( let v3 =
                    coe
                      MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                      (coe v0)
               in coe
                    ( let v4 =
                            coe
                              MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                              (coe v3)
                       in coe
                            ( coe
                                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                ( MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
                                        (coe v4)
                                    )
                                )
                                ( coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (\v5 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                                    (\v5 v6 -> v5)
                                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v1)
                                        (coe v2)
                                    )
                                )
                            )
                    )
            )
            erased
        )
    )

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-singleton⁻
d_'8712''8342''7525''45'singleton'8315'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8712''8342''7525''45'singleton'8315'_332
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  v10 =
    du_'8712''8342''7525''45'singleton'8315'_332 v10
du_'8712''8342''7525''45'singleton'8315'_332 ::
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8712''8342''7525''45'singleton'8315'_332 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336 v3 ->
      coe
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_singleton'8315'_1450
        (coe v3)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.≈-lookup
d_'8776''45'lookup_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  AgdaAny
d_'8776''45'lookup_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 =
  du_'8776''45'lookup_338 v8 v9
du_'8776''45'lookup_338 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  AgdaAny
du_'8776''45'lookup_338 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336 v4 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.C_tree_262 v5 v6 ->
          coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_lookup'45'result_318
                (coe v6)
                (coe v4)
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-insert⁺
d_'8712''8342''7525''45'insert'8314'_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'insert'8314'_342
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  ~v8
  v9
  v10
  ~v11
  v12 =
    du_'8712''8342''7525''45'insert'8314'_342 v3 v5 v9 v10 v12
du_'8712''8342''7525''45'insert'8314'_342 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
du_'8712''8342''7525''45'insert'8314'_342 v0 v1 v2 v3 v4 =
  case coe v2 of
    MAlonzo.Code.Data.Tree.AVL.C_tree_262 v5 v6 ->
      case coe v4 of
        MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336 v9 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_insert'8314'_2318
                v0
                (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
                v1
                v3
                v6
                ( coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    ( coe
                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                        ( coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24
                        )
                    )
                    ( coe
                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30
                    )
                )
                v9
                erased
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties._.k′≉key-p
d_k'8242''8777'key'45'p_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_k'8242''8777'key'45'p_358 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-insert⁺⁺
d_'8712''8342''7525''45'insert'8314''8314'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'insert'8314''8314'_362
  ~v0
  ~v1
  ~v2
  v3
  v4
  ~v5
  ~v6
  v7
  v8 =
    du_'8712''8342''7525''45'insert'8314''8314'_362 v3 v4 v7 v8
du_'8712''8342''7525''45'insert'8314''8314'_362 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
du_'8712''8342''7525''45'insert'8314''8314'_362 v0 v1 v2 v3 =
  case coe v3 of
    MAlonzo.Code.Data.Tree.AVL.C_tree_262 v4 v5 ->
      let v6 =
            coe
              MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_any'63'_324
              ( coe
                  ( \v6 ->
                      coe
                        MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562
                        ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                            (coe v0)
                        )
                        v1
                        (MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v6))
                  )
              )
              (coe v5)
       in coe
            ( case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8 ->
                  if coe v7
                    then case coe v8 of
                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9 ->
                        coe
                          MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336
                          ( coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_Any'45'insert'45'just_1996
                              v0
                              (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
                              v1
                              v2
                              v5
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  ( coe
                                      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                      ( coe
                                          MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24
                                      )
                                  )
                                  ( coe
                                      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30
                                  )
                              )
                              ( \v10 v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe v11)
                                    erased
                              )
                              v9
                          )
                      _ -> MAlonzo.RTE.mazUnreachableError
                    else
                      coe
                        seq
                        (coe v8)
                        ( coe
                            MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_Any'45'insert'45'nothing_1986
                                v0
                                (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
                                v1
                                v2
                                v5
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24
                                        )
                                    )
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30
                                    )
                                )
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    ( let v9 =
                                            coe
                                              MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                                              (coe v0)
                                       in coe
                                            ( let v10 =
                                                    coe
                                                      MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                                                      (coe v9)
                                               in coe
                                                    ( coe
                                                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                        ( MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
                                                            ( coe
                                                                MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
                                                                (coe v10)
                                                            )
                                                        )
                                                        v1
                                                    )
                                            )
                                    )
                                    erased
                                )
                                erased
                            )
                        )
                _ -> MAlonzo.RTE.mazUnreachableError
            )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.≈ₖᵥ-Resp
d_'8776''8342''7525''45'Resp_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8776''8342''7525''45'Resp_390
  ~v0
  ~v1
  ~v2
  v3
  v4
  v5
  ~v6
  ~v7
  v8
  v9
  v10
  v11 =
    du_'8776''8342''7525''45'Resp_390 v3 v4 v5 v8 v9 v10 v11
du_'8776''8342''7525''45'Resp_390 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8776''8342''7525''45'Resp_390 v0 v1 v2 v3 v4 v5 v6 =
  case coe v6 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8 ->
      coe
        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
        ( let v9 =
                coe
                  MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                  (coe v0)
           in coe
                ( let v10 =
                        coe
                          MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                          (coe v9)
                   in coe
                        ( let v11 =
                                coe
                                  MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                                  (coe v10)
                           in coe
                                ( coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v11))
                                    ( coe
                                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                        (\v12 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12))
                                        (\v12 v13 -> v12)
                                        v3
                                        ( coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe v2)
                                            (coe v4)
                                        )
                                    )
                                    ( coe
                                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                        (\v12 v13 -> v13)
                                        (\v12 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12))
                                        v3
                                        ( coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe v2)
                                            (coe v4)
                                        )
                                    )
                                    v1
                                    v7
                                    ( let v12 =
                                            coe
                                              MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                                              (coe v0)
                                       in coe
                                            ( let v13 =
                                                    coe
                                                      MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                                                      (coe v12)
                                               in coe
                                                    ( let v14 =
                                                            coe
                                                              MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                                                              (coe v13)
                                                       in coe
                                                            ( coe
                                                                MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                                ( MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                    (coe v14)
                                                                )
                                                                v1
                                                                v2
                                                                v5
                                                            )
                                                    )
                                            )
                                    )
                                )
                        )
                )
        )
        (coe v8)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-insert⁻
d_'8712''8342''7525''45'insert'8315'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8712''8342''7525''45'insert'8315'_400
  ~v0
  ~v1
  ~v2
  v3
  v4
  ~v5
  ~v6
  v7
  v8
  v9
  v10
  v11 =
    du_'8712''8342''7525''45'insert'8315'_400 v3 v4 v7 v8 v9 v10 v11
du_'8712''8342''7525''45'insert'8315'_400 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8712''8342''7525''45'insert'8315'_400 v0 v1 v2 v3 v4 v5 v6 =
  case coe v5 of
    MAlonzo.Code.Data.Tree.AVL.C_tree_262 v7 v8 ->
      case coe v6 of
        MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336 v11 ->
          let v12 =
                coe
                  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_insert'8315'_2356
                  (coe v0)
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
                  ( coe
                      ( \v12 v13 ->
                          coe
                            du_'8776''8342''7525''45'Resp_390
                            (coe v0)
                            (coe v12)
                            (coe v13)
                            ( coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe v1)
                                (coe v2)
                            )
                      )
                  )
                  (coe v3)
                  (coe v4)
                  (coe v8)
                  ( coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      ( coe
                          MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                          ( coe
                              MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24
                          )
                      )
                      ( coe
                          MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30
                      )
                  )
                  (coe v11)
           in coe
                ( case coe v12 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13 -> coe v12
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13 ->
                      coe
                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                        ( coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            ( coe
                                ( \v14 ->
                                    coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      ( coe
                                          MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_lookup'45'result_318
                                          (coe v8)
                                          (coe v13)
                                      )
                                      ( let v15 =
                                              coe
                                                MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                                                (coe v0)
                                         in coe
                                              ( let v16 =
                                                      coe
                                                        MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                                                        (coe v15)
                                                 in coe
                                                      ( let v17 =
                                                              coe
                                                                MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                                                                (coe v16)
                                                         in coe
                                                              ( coe
                                                                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                  ( MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                      (coe v17)
                                                                  )
                                                                  v3
                                                                  v1
                                                                  ( MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                                                                      ( coe
                                                                          MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
                                                                          (coe v8)
                                                                          (coe v13)
                                                                      )
                                                                  )
                                                                  ( let v18 =
                                                                          coe
                                                                            MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                                                                            (coe v0)
                                                                     in coe
                                                                          ( let v19 =
                                                                                  coe
                                                                                    MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                                                                                    (coe v18)
                                                                             in coe
                                                                                  ( let v20 =
                                                                                          coe
                                                                                            MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                                                                                            (coe v19)
                                                                                     in coe
                                                                                          ( coe
                                                                                              MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                                                              ( MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                                  (coe v20)
                                                                                              )
                                                                                              v1
                                                                                              v3
                                                                                              v14
                                                                                          )
                                                                                  )
                                                                          )
                                                                  )
                                                                  ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                      ( coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                          ( coe
                                                                              MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_lookup'45'result_318
                                                                              (coe v8)
                                                                              (coe v13)
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                      )
                                              )
                                      )
                                )
                            )
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_map_250
                                    (coe v8)
                                    ( coe
                                        ( \v14 v15 ->
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15)
                                        )
                                    )
                                    (coe v13)
                                )
                            )
                        )
                    _ -> MAlonzo.RTE.mazUnreachableError
                )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-lookup⁺
d_'8712''8342''7525''45'lookup'8314'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8712''8342''7525''45'lookup'8314'_430 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-lookup⁻
d_'8712''8342''7525''45'lookup'8315'_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'lookup'8315'_468
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  v6
  v7
  v8
  ~v9 =
    du_'8712''8342''7525''45'lookup'8315'_468 v3 v6 v7 v8
du_'8712''8342''7525''45'lookup'8315'_468 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
du_'8712''8342''7525''45'lookup'8315'_468 v0 v1 v2 v3 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.C_tree_262 v4 v5 ->
      coe
        MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.C_tree_336
        ( coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_map_250
            (coe v5)
            ( coe
                ( \v6 ->
                    coe
                      MAlonzo.Code.Data.Product.Base.du_map_128
                      ( let v7 =
                              coe
                                MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                                (coe v0)
                         in coe
                              ( let v8 =
                                      coe
                                        MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                                        (coe v7)
                                 in coe
                                      ( let v9 =
                                              coe
                                                MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                                                (coe v8)
                                         in coe
                                              ( coe
                                                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                  ( MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                      (coe v9)
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                      (\v10 v11 -> v11)
                                                      (\v10 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v2)
                                                          (coe v3)
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v6))
                                                          ( coe
                                                              MAlonzo.Code.Data.Tree.AVL.Value.d_value_68
                                                              (coe v6)
                                                          )
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                      (\v10 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))
                                                      (\v10 v11 -> v10)
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v2)
                                                          (coe v3)
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v6))
                                                          ( coe
                                                              MAlonzo.Code.Data.Tree.AVL.Value.d_value_68
                                                              (coe v6)
                                                          )
                                                      )
                                                  )
                                              )
                                      )
                              )
                      )
                      erased
                )
            )
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.du_lookup'8315'_3000
                (coe v0)
                (coe v5)
                (coe v2)
                ( coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    ( coe
                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                        ( coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24
                        )
                    )
                    ( coe
                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30
                    )
                )
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-lookup-nothing⁺
d_'8712''8342''7525''45'lookup'45'nothing'8314'_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ( AgdaAny ->
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8712''8342''7525''45'lookup'45'nothing'8314'_480 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-lookup-nothing⁻
d_'8712''8342''7525''45'lookup'45'nothing'8315'_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8712''8342''7525''45'lookup'45'nothing'8315'_514 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∈ₖᵥ-member
d_'8712''8342''7525''45'member_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8712''8342''7525''45'member_528 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.∉ₖᵥ-member
d_'8713''8342''7525''45'member_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ( AgdaAny ->
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8713''8342''7525''45'member_532 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.member-∈ₖᵥ
d_member'45''8712''8342''7525'_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_member'45''8712''8342''7525'_536 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 ~v8 =
  du_member'45''8712''8342''7525'_536 v3 v4 v7
du_member'45''8712''8342''7525'_536 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_member'45''8712''8342''7525'_536 v0 v1 v2 =
  let v3 =
        coe MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_208 v0 v2 v1
   in coe
        ( case coe v3 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 ->
              coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe v4)
                ( coe
                    du_'8712''8342''7525''45'lookup'8315'_468
                    (coe v0)
                    (coe v2)
                    (coe v1)
                    (coe v4)
                )
            _ -> MAlonzo.RTE.mazUnreachableError
        )

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.member-∉ₖᵥ
d_member'45''8713''8342''7525'_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_member'45''8713''8342''7525'_560 = erased

-- Data.Tree.AVL.Map.Membership.Propositional.Properties.member-Reflects-∈ₖᵥ
d_member'45'Reflects'45''8712''8342''7525'_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
d_member'45'Reflects'45''8712''8342''7525'_586
  ~v0
  ~v1
  ~v2
  v3
  v4
  ~v5
  ~v6
  v7 =
    du_member'45'Reflects'45''8712''8342''7525'_586 v3 v4 v7
du_member'45'Reflects'45''8712''8342''7525'_586 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
du_member'45'Reflects'45''8712''8342''7525'_586 v0 v1 v2 =
  let v3 =
        coe MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_208 v0 v2 v1
   in coe
        ( case coe v3 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 ->
              coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                ( coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe v4)
                    ( coe
                        du_'8712''8342''7525''45'lookup'8315'_468
                        (coe v0)
                        (coe v2)
                        (coe v1)
                        (coe v4)
                    )
                )
            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 ->
              coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
            _ -> MAlonzo.RTE.mazUnreachableError
        )
