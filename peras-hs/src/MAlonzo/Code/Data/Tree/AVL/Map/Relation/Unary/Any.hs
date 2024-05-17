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

module MAlonzo.Code.Data.Tree.AVL.Map.Relation.Unary.Any where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
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

-- Data.Tree.AVL.Map.Relation.Unary.Any._.Map
d_Map_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ()
d_Map_102 = erased

-- Data.Tree.AVL.Map.Relation.Unary.Any.Mapₚ.Any
d_Any_110 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

-- Data.Tree.AVL.Map.Relation.Unary.Any.Any
d_Any_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ()
d_Any_146 = erased

-- Data.Tree.AVL.Map.Relation.Unary.Any.map
d_map_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_map_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 =
  du_map_150 v10 v11
du_map_150 ::
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
du_map_150 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_map_338
    (coe v1)
    ( coe
        ( \v2 ->
            coe
              v0
              ( coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v2))
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v2))
              )
        )
    )

-- Data.Tree.AVL.Map.Relation.Unary.Any.lookup
d_lookup_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookup_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_lookup_154 v8
du_lookup_154 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookup_154 v0 =
  coe
    MAlonzo.Code.Function.Base.du__'8728''8242'__216
    (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_80)
    ( coe
        MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_lookup_344
        (coe v0)
    )

-- Data.Tree.AVL.Map.Relation.Unary.Any.lookupKey
d_lookupKey_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  AgdaAny
d_lookupKey_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 =
  du_lookupKey_156 v8
du_lookupKey_156 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  AgdaAny
du_lookupKey_156 v0 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_lookupKey_348
    (coe v0)

-- Data.Tree.AVL.Map.Relation.Unary.Any.satisfied
d_satisfied_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfied_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 =
  du_satisfied_158 v8
du_satisfied_158 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfied_158 v0 =
  coe
    MAlonzo.Code.Function.Base.du__'8728''8242'__216
    ( coe
        MAlonzo.Code.Data.Product.Base.du_map_128
        (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_80)
        (coe (\v1 v2 -> v2))
    )
    ( coe
        MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_satisfied_352
        (coe v0)
    )

-- Data.Tree.AVL.Map.Relation.Unary.Any.any?
d_any'63'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  ( MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any'63'_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 =
  du_any'63'_160 v8
du_any'63'_160 ::
  ( MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_any'63'_160 v0 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_any'63'_356
    ( coe
        ( \v1 ->
            coe
              v0
              ( coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v1))
                  (coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v1))
              )
        )
    )

-- Data.Tree.AVL.Map.Relation.Unary.Any.satisfiable
d_satisfiable_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 =
  du_satisfiable_164 v8
du_satisfiable_164 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_164 v0 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2 ->
      case coe v1 of
        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.du_satisfiable_370
            (coe v3)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v2))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError
