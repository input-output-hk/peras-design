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

module MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Tree.AVL.Height
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
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

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._._<⁺_
d__'60''8314'__104 a0 a1 a2 a3 a4 a5 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.K&_
d_K'38'__106 a0 a1 a2 a3 a4 a5 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.Key⁺
d_Key'8314'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  ()
d_Key'8314'_108 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.Tree
d_Tree_110 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.Value
d_Value_112 a0 a1 a2 a3 a4 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.Height._∼_⊔_
d__'8764'_'8852'__146 a0 a1 a2 a3 a4 a5 a6 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Any
d_Any_192 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_Any_192
  = C_here_216 AgdaAny
  | C_left_232 T_Any_192
  | C_right_248 T_Any_192

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.map
d_map_250 ::
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
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Any_192 ->
  T_Any_192
d_map_250
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
  ~v11
  ~v12
  v13
  v14
  v15 =
    du_map_250 v13 v14 v15
du_map_250 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    AgdaAny ->
    AgdaAny
  ) ->
  T_Any_192 ->
  T_Any_192
du_map_250 v0 v1 v2 =
  case coe v2 of
    C_here_216 v7 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v11 v12 v14 v15 v16 v17 ->
          coe C_here_216 (coe v1 v14 v7)
        _ -> MAlonzo.RTE.mazUnreachableError
    C_left_232 v8 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v11 v12 v14 v15 v16 v17 ->
          coe C_left_232 (coe du_map_250 (coe v15) (coe v1) (coe v8))
        _ -> MAlonzo.RTE.mazUnreachableError
    C_right_248 v9 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v11 v12 v14 v15 v16 v17 ->
          coe C_right_248 (coe du_map_250 (coe v16) (coe v1) (coe v9))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.lookup
d_lookup_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
d_lookup_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 =
  du_lookup_264 v11 v12
du_lookup_264 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
du_lookup_264 v0 v1 =
  case coe v1 of
    C_here_216 v6 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe v13
        _ -> MAlonzo.RTE.mazUnreachableError
    C_left_232 v7 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe du_lookup_264 (coe v14) (coe v7)
        _ -> MAlonzo.RTE.mazUnreachableError
    C_right_248 v8 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe du_lookup_264 (coe v15) (coe v8)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.lookupKey
d_lookupKey_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_192 ->
  AgdaAny
d_lookupKey_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 =
  du_lookupKey_272 v11
du_lookupKey_272 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_192 ->
  AgdaAny
du_lookupKey_272 v0 =
  coe
    MAlonzo.Code.Function.Base.du__'8728''8242'__216
    (coe (\v1 -> MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v1)))
    (coe du_lookup_264 (coe v0))

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.satisfied
d_satisfied_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_192 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfied_274
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
  v11
  v12 =
    du_satisfied_274 v11 v12
du_satisfied_274 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  T_Any_192 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfied_274 v0 v1 =
  case coe v1 of
    C_here_216 v6 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe
            MAlonzo.Code.Data.Product.Base.du_'45''44'__92
            (coe v13)
            (coe v6)
        _ -> MAlonzo.RTE.mazUnreachableError
    C_left_232 v7 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe du_satisfied_274 (coe v14) (coe v7)
        _ -> MAlonzo.RTE.mazUnreachableError
    C_right_248 v8 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe du_satisfied_274 (coe v15) (coe v8)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.toSum
d_toSum_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_toSum_306
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
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  v17 =
    du_toSum_306 v17
du_toSum_306 ::
  T_Any_192 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_toSum_306 v0 =
  case coe v0 of
    C_here_216 v5 ->
      coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5)
    C_left_232 v6 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v6))
    C_right_248 v7 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v7))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any._.fromSum
d_fromSum_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Any_192
d_fromSum_314
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
  ~v11
  ~v12
  ~v13
  ~v14
  ~v15
  ~v16
  v17 =
    du_fromSum_314 v17
du_fromSum_314 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Any_192
du_fromSum_314 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe C_here_216 v1
    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 ->
      case coe v1 of
        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe C_left_232 v2
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe C_right_248 v2
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.any?
d_any'63'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any'63'_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 =
  du_any'63'_324 v11 v12
du_any'63'_324 ::
  ( MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_any'63'_324 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 v2 ->
      coe
        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v2 v3 v5 v6 v7 v8 ->
      coe
        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_150
        (coe du_fromSum_314)
        ( coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__84
            (coe v0 v5)
            ( coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__84
                (coe du_any'63'_324 (coe v0) (coe v6))
                (coe du_any'63'_324 (coe v0) (coe v7))
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.satisfiable
d_satisfiable_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_346
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  v8
  ~v9
  ~v10
  v11
  v12
  v13 =
    du_satisfiable_346 v8 v11 v12 v13
du_satisfiable_346 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_346 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
    ( coe
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208
        (0 :: Integer)
        (0 :: Integer)
        ( coe
            MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70
            (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
        )
        (coe MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 (coe v1))
        (coe MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 (coe v2))
        (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38)
    )
    ( coe
        C_here_216
        (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
    )
