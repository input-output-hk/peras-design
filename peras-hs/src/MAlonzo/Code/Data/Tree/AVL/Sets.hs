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

module MAlonzo.Code.Data.Tree.AVL.Sets where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Map
import qualified MAlonzo.Code.Function.Base
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

-- Data.Tree.AVL.Sets.⟨Set⟩
d_'10216'Set'10217'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  ()
d_'10216'Set'10217'_148 = erased

-- Data.Tree.AVL.Sets.empty
d_empty_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_empty_150 ~v0 ~v1 ~v2 ~v3 = du_empty_150
du_empty_150 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_empty_150 = coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_198

-- Data.Tree.AVL.Sets.singleton
d_singleton_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_singleton_152 ~v0 ~v1 ~v2 ~v3 v4 = du_singleton_152 v4
du_singleton_152 ::
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_singleton_152 v0 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_singleton_200
    v0
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Data.Tree.AVL.Sets.insert
d_insert_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insert_156 ~v0 ~v1 ~v2 v3 v4 = du_insert_156 v3 v4
du_insert_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_insert_156 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
    v0
    v1
    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)

-- Data.Tree.AVL.Sets.delete
d_delete_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_delete_160 ~v0 ~v1 ~v2 v3 = du_delete_160 v3
du_delete_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_delete_160 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_delete_206 (coe v0)

-- Data.Tree.AVL.Sets.member
d_member_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Bool
d_member_162 ~v0 ~v1 ~v2 v3 = du_member_162 v3
du_member_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Bool
du_member_162 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_member_214 (coe v0)

-- Data.Tree.AVL.Sets.headTail
d_headTail_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_164 ~v0 ~v1 ~v2 v3 v4 = du_headTail_164 v3 v4
du_headTail_164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_headTail_164 v0 v1 =
  coe
    MAlonzo.Code.Data.Maybe.Base.du_map_68
    ( coe
        MAlonzo.Code.Data.Product.Base.du_map'8321'_138
        (coe (\v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
    )
    (coe MAlonzo.Code.Data.Tree.AVL.Map.du_headTail_216 v0 v1)

-- Data.Tree.AVL.Sets.initLast
d_initLast_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_168 ~v0 ~v1 ~v2 v3 v4 = du_initLast_168 v3 v4
du_initLast_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_168 v0 v1 =
  coe
    MAlonzo.Code.Data.Maybe.Base.du_map_68
    ( coe
        MAlonzo.Code.Data.Product.Base.du_map'8322'_150
        ( coe
            (\v2 v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
        )
    )
    (coe MAlonzo.Code.Data.Tree.AVL.Map.du_initLast_218 v0 v1)

-- Data.Tree.AVL.Sets.fromList
d_fromList_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_fromList_172 ~v0 ~v1 ~v2 v3 v4 = du_fromList_172 v3 v4
du_fromList_172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_fromList_172 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_fromList_226
    v0
    ( coe
        MAlonzo.Code.Data.List.Base.du_map_22
        ( coe
            ( \v2 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe v2)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            )
        )
        (coe v1)
    )

-- Data.Tree.AVL.Sets.toList
d_toList_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  [AgdaAny]
d_toList_176 ~v0 ~v1 ~v2 ~v3 v4 = du_toList_176 v4
du_toList_176 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> [AgdaAny]
du_toList_176 v0 =
  coe
    MAlonzo.Code.Data.List.Base.du_map_22
    (coe (\v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
    (coe MAlonzo.Code.Data.Tree.AVL.Map.du_toList_228 v0)

-- Data.Tree.AVL.Sets.foldr
d_foldr_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny
d_foldr_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_foldr_178 v6 v7
du_foldr_178 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny
du_foldr_178 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_foldr_220
    ( coe
        MAlonzo.Code.Function.Base.du__'8728''8242'__216
        (coe (\v2 v3 -> v2))
        (coe v0)
    )
    v1

-- Data.Tree.AVL.Sets.size
d_size_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Integer
d_size_184 ~v0 ~v1 ~v2 ~v3 = du_size_184
du_size_184 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Integer
du_size_184 = coe MAlonzo.Code.Data.Tree.AVL.Map.du_size_230

-- Data.Tree.AVL.Sets.union
d_union_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_union_186 ~v0 ~v1 ~v2 v3 = du_union_186 v3
du_union_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_union_186 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_union_236 (coe v0)

-- Data.Tree.AVL.Sets.unions
d_unions_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_unions_188 ~v0 ~v1 ~v2 v3 = du_unions_188 v3
du_unions_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_unions_188 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_unions_242 (coe v0)

-- Data.Tree.AVL.Sets.intersection
d_intersection_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_intersection_190 ~v0 ~v1 ~v2 v3 = du_intersection_190 v3
du_intersection_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_intersection_190 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_intersection_248 (coe v0)

-- Data.Tree.AVL.Sets.intersections
d_intersections_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_intersections_192 ~v0 ~v1 ~v2 v3 = du_intersections_192 v3
du_intersections_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_intersections_192 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Map.du_intersections_254 (coe v0)

-- Data.Tree.AVL.Sets._∈?_
d__'8712''63'__194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Bool
d__'8712''63'__194 ~v0 ~v1 ~v2 v3 = du__'8712''63'__194 v3
du__'8712''63'__194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Bool
du__'8712''63'__194 v0 = coe du_member_162 (coe v0)
