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

module MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Height
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
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

-- Data.Tree.AVL.Relation.Unary.Any.Indexed.K&_
d_K'38'__108 a0 a1 a2 a3 a4 a5 = ()

-- Data.Tree.AVL.Relation.Unary.Any._.Tree
d_Tree_254 a0 a1 a2 a3 a4 a5 = ()

-- Data.Tree.AVL.Relation.Unary.Any._.Value
d_Value_256 a0 a1 a2 a3 a4 = ()

-- Data.Tree.AVL.Relation.Unary.Any.AVLₚ.Any
d_Any_272 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()

-- Data.Tree.AVL.Relation.Unary.Any.Any
d_Any_326 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
newtype T_Any_326
  = C_tree_336 MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192

-- Data.Tree.AVL.Relation.Unary.Any.map
d_map_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Any_326 ->
  T_Any_326
d_map_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 =
  du_map_338 v10 v11 v12
du_map_338 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Any_326 ->
  T_Any_326
du_map_338 v0 v1 v2 =
  case coe v2 of
    C_tree_336 v5 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.C_tree_262 v6 v7 ->
          coe
            C_tree_336
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_map_250
                (coe v7)
                (coe v1)
                (coe v5)
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Relation.Unary.Any.lookup
d_lookup_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
d_lookup_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 =
  du_lookup_344 v8 v9
du_lookup_344 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
du_lookup_344 v0 v1 =
  case coe v1 of
    C_tree_336 v4 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.C_tree_262 v5 v6 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
            (coe v6)
            (coe v4)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Relation.Unary.Any.lookupKey
d_lookupKey_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_Any_326 ->
  AgdaAny
d_lookupKey_348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 =
  du_lookupKey_348 v8 v9
du_lookupKey_348 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> T_Any_326 -> AgdaAny
du_lookupKey_348 v0 v1 =
  case coe v1 of
    C_tree_336 v4 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.C_tree_262 v5 v6 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookupKey_272
            v6
            v4
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Relation.Unary.Any.satisfied
d_satisfied_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfied_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 =
  du_satisfied_352 v8 v9
du_satisfied_352 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfied_352 v0 v1 =
  case coe v1 of
    C_tree_336 v4 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.C_tree_262 v5 v6 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_satisfied_274
            (coe v6)
            (coe v4)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Relation.Unary.Any.any?
d_any'63'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any'63'_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 =
  du_any'63'_356 v8 v9
du_any'63'_356 ::
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_any'63'_356 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.C_tree_262 v2 v3 ->
      coe
        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_150
        (coe C_tree_336)
        ( coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_any'63'_324
            (coe v0)
            (coe v3)
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Relation.Unary.Any..extendedlambda0
d_'46'extendedlambda0_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_'46'extendedlambda0_362
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
  ~v10
  v11 =
    du_'46'extendedlambda0_362 v11
du_'46'extendedlambda0_362 ::
  T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_'46'extendedlambda0_362 v0 =
  case coe v0 of
    C_tree_336 v3 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Relation.Unary.Any.satisfiable
d_satisfiable_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 =
  du_satisfiable_370 v8 v9
du_satisfiable_370 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_370 v0 v1 =
  coe
    MAlonzo.Code.Data.Product.Base.du_map_128
    (coe MAlonzo.Code.Data.Tree.AVL.C_tree_262 (coe (1 :: Integer)))
    (\v2 v3 -> coe C_tree_336 v3)
    ( coe
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_satisfiable_346
        (coe v0)
        ( coe
            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
            ( coe
                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24
            )
        )
        ( coe
            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30
        )
        (coe v1)
    )
