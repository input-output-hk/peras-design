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

module MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Tree.AVL.Height
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Key
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
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

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL._<_<_
d__'60'_'60'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  ()
d__'60'_'60'__28 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.K&_
d_K'38'__34 a0 a1 a2 a3 a4 a5 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.Key⁺
d_Key'8314'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  ()
d_Key'8314'_36 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.Tree
d_Tree_40 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.Value
d_Value_42 a0 a1 a2 a3 a4 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.insert
d_insert_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_insert_62 ~v0 ~v1 ~v2 v3 = du_insert_62 v3
du_insert_62 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_insert_62 v0 v1 v2 v3 v4 v5 v6 v7 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_920
    (coe v0)
    v2
    v6
    v7

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.insertWith
d_insertWith_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_insertWith_64 ~v0 ~v1 ~v2 v3 = du_insertWith_64 v3
du_insertWith_64 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_insertWith_64 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
    (coe v0)
    v2
    v6
    v7
    v8
    v9

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.joinʳ⁺
d_join'691''8314'_70 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'691''8314'_70 ~v0 ~v1 ~v2 ~v3 = du_join'691''8314'_70
du_join'691''8314'_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'691''8314'_70 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.du_join'691''8314'_456
    v4
    v5
    v7
    v8
    v9
    v10

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.joinˡ⁺
d_join'737''8314'_74 ::
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'737''8314'_74 ~v0 ~v1 ~v2 ~v3 = du_join'737''8314'_74
du_join'737''8314'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'737''8314'_74 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.du_join'737''8314'_366
    v4
    v5
    v7
    v8
    v9
    v10

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.lookup
d_lookup_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe AgdaAny
d_lookup_84 ~v0 ~v1 ~v2 v3 = du_lookup_84 v3
du_lookup_84 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe AgdaAny
du_lookup_84 v0 v1 v2 v3 v4 v5 v6 v7 v8 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.du_lookup_1034
    (coe v0)
    v2
    v6
    v7
    v8

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.singleton
d_singleton_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180
d_singleton_96 ~v0 ~v1 ~v2 ~v3 = du_singleton_96
du_singleton_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180
du_singleton_96 v0 v1 v2 v3 v4 v5 v6 =
  coe MAlonzo.Code.Data.Tree.AVL.Indexed.du_singleton_798 v4 v5 v6

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.Height._∼_⊔_
d__'8764'_'8852'__150 a0 a1 a2 a3 a4 a5 a6 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AVL.Height._⊕_
d__'8853'__152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  Integer
d__'8853'__152 ~v0 = du__'8853'__152
du__'8853'__152 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer -> Integer
du__'8853'__152 =
  coe MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Any.Any
d_Any_180 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Any.lookup
d_lookup_190 ::
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
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
d_lookup_190 ~v0 ~v1 ~v2 ~v3 = du_lookup_190
du_lookup_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
du_lookup_190 v0 v1 v2 v3 v4 v5 v6 v7 v8 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
    v7
    v8

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Any.lookupKey
d_lookupKey_192 ::
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
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
d_lookupKey_192 ~v0 ~v1 ~v2 ~v3 = du_lookupKey_192
du_lookupKey_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_lookupKey_192 v0 v1 v2 v3 v4 v5 v6 v7 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookupKey_272
    v7

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.Eq._≉_
d__'8777'__264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  ()
d__'8777'__264 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.Eq.sym
d_sym_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_sym_286 ~v0 ~v1 ~v2 v3 = du_sym_286 v3
du_sym_286 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
du_sym_286 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
          (coe v0)
   in coe
        ( let v2 =
                coe
                  MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                  (coe v1)
           in coe
                ( let v3 =
                        coe
                          MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                          (coe v2)
                   in coe
                        ( coe
                            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                            ( coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (coe v3)
                            )
                        )
                )
        )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.lookup-result
d_lookup'45'result_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
d_lookup'45'result_318
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
    du_lookup'45'result_318 v11 v12
du_lookup'45'result_318 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_lookup'45'result_318 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v6 ->
      coe v6
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v7 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe du_lookup'45'result_318 (coe v14) (coe v7)
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v8 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v10 v11 v13 v14 v15 v16 ->
          coe du_lookup'45'result_318 (coe v15) (coe v8)
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.lookup-bounded
d_lookup'45'bounded_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookup'45'bounded_330
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  v6
  v7
  ~v8
  ~v9
  ~v10
  v11
  v12 =
    du_lookup'45'bounded_330 v3 v6 v7 v11 v12
du_lookup'45'bounded_330 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookup'45'bounded_330 v0 v1 v2 v3 v4 =
  case coe v3 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v5 v6 v8 v9 v10 v11 ->
      case coe v4 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v16 ->
          coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.du_ordered_224
                (coe v0)
                (coe v1)
                ( coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        ( coe
                            MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208
                                    v5
                                    v6
                                    v8
                                    v9
                                    v10
                                    v11
                                )
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                    v16
                                )
                            )
                        )
                    )
                )
                (coe v9)
            )
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.du_ordered_224
                (coe v0)
                ( coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        ( coe
                            MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208
                                    v5
                                    v6
                                    v8
                                    v9
                                    v10
                                    v11
                                )
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                    v16
                                )
                            )
                        )
                    )
                )
                (coe v2)
                (coe v10)
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v17 ->
          coe
            MAlonzo.Code.Data.Product.Base.du_map'8322'_150
            ( \v20 v21 ->
                coe
                  MAlonzo.Code.Data.Tree.AVL.Key.du_trans'8314'_108
                  v0
                  ( coe
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                      ( coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          ( coe
                              MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                              ( coe
                                  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
                                  ( coe
                                      MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208
                                      v5
                                      v6
                                      v8
                                      v9
                                      v10
                                      v11
                                  )
                                  ( coe
                                      MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                      v17
                                  )
                              )
                          )
                      )
                  )
                  ( coe
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                      ( coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v8))
                      )
                  )
                  v2
                  v21
                  ( coe
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_ordered_224
                      (coe v0)
                      ( coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          ( coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v8))
                          )
                      )
                      (coe v2)
                      (coe v10)
                  )
            )
            ( coe
                du_lookup'45'bounded_330
                (coe v0)
                (coe v1)
                ( coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v8))
                    )
                )
                (coe v9)
                (coe v17)
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v18 ->
          coe
            MAlonzo.Code.Data.Product.Base.du_map'8321'_138
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Key.du_trans'8314'_108
                v0
                v1
                ( coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v8))
                    )
                )
                ( coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        ( coe
                            MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_lookup_264
                                (coe v10)
                                (coe v18)
                            )
                        )
                    )
                )
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_ordered_224
                    (coe v0)
                    (coe v1)
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        ( coe
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                            (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v8))
                        )
                    )
                    (coe v9)
                )
            )
            ( coe
                du_lookup'45'bounded_330
                (coe v0)
                ( coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    ( coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v8))
                    )
                )
                (coe v2)
                (coe v10)
                (coe v18)
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.lookup-rebuild
d_lookup'45'rebuild_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_lookup'45'rebuild_366
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
    du_lookup'45'rebuild_366 v13 v14 v15
du_lookup'45'rebuild_366 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_lookup'45'rebuild_366 v0 v1 v2 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v7 ->
      coe
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
        v2
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v8 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v11 v12 v14 v15 v16 v17 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
            (coe du_lookup'45'rebuild_366 (coe v15) (coe v8) (coe v2))
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v9 ->
      case coe v0 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v11 v12 v14 v15 v16 v17 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
            (coe du_lookup'45'rebuild_366 (coe v16) (coe v9) (coe v2))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.lookup-rebuild-accum
d_lookup'45'rebuild'45'accum_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_lookup'45'rebuild'45'accum_382
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
    du_lookup'45'rebuild'45'accum_382 v13 v14 v15
du_lookup'45'rebuild'45'accum_382 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_lookup'45'rebuild'45'accum_382 v0 v1 v2 =
  coe
    du_lookup'45'rebuild_366
    (coe v0)
    (coe v1)
    ( coe
        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
        (coe v2)
        (coe du_lookup'45'result_318 (coe v0) (coe v1))
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinˡ⁺-here⁺
d_join'737''8314''45'here'8314'_408 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_join'737''8314''45'here'8314'_408
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
  v14
  ~v15
  v16
  v17 =
    du_join'737''8314''45'here'8314'_408 v14 v16 v17
du_join'737''8314''45'here'8314'_408 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_join'737''8314''45'here'8314'_408 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
            v2
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 ->
          coe
            seq
            (coe v6)
            ( case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  case coe v4 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe
                            seq
                            (coe v13)
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                    v2
                                )
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v2
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v2
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinˡ⁺-left⁺
d_join'737''8314''45'left'8314'_498 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_join'737''8314''45'left'8314'_498
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
  v14
  ~v15
  v16
  v17 =
    du_join'737''8314''45'left'8314'_498 v14 v16 v17
du_join'737''8314''45'left'8314'_498 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_join'737''8314''45'left'8314'_498 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
            v2
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 ->
          coe
            seq
            (coe v6)
            ( case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  case coe v4 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe
                            seq
                            (coe v13)
                            ( case coe v2 of
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v20 ->
                                  coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                    ( coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                        v20
                                    )
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v21 ->
                                  coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                    ( coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                        v21
                                    )
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v22 ->
                                  case coe v22 of
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v28 ->
                                      coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                        v28
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v29 ->
                                      coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                        ( coe
                                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                            v29
                                        )
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v30 ->
                                      coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                        ( coe
                                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                            v30
                                        )
                                    _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          case coe v2 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v20 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v20
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v21 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                v21
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v22 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                    v22
                                )
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          case coe v2 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v20 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v20
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v21 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                v21
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v22 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                    v22
                                )
                            _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinˡ⁺-right⁺
d_join'737''8314''45'right'8314'_712 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_join'737''8314''45'right'8314'_712
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
  v14
  ~v15
  v16
  v17 =
    du_join'737''8314''45'right'8314'_712 v14 v16 v17
du_join'737''8314''45'right'8314'_712 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_join'737''8314''45'right'8314'_712 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
            v2
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 ->
          coe
            seq
            (coe v6)
            ( case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  case coe v4 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe
                            seq
                            (coe v13)
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                    v2
                                )
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                v2
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                v2
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinʳ⁺-here⁺
d_join'691''8314''45'here'8314'_802 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_join'691''8314''45'here'8314'_802
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
  v15
  v16
  v17 =
    du_join'691''8314''45'here'8314'_802 v15 v16 v17
du_join'691''8314''45'here'8314'_802 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_join'691''8314''45'here'8314'_802 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
            v2
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 ->
          coe
            seq
            (coe v6)
            ( case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  case coe v4 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v2
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v2
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe
                            seq
                            (coe v12)
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                    v2
                                )
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v2
                _ -> MAlonzo.RTE.mazUnreachableError
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinʳ⁺-left⁺
d_join'691''8314''45'left'8314'_892 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_join'691''8314''45'left'8314'_892
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
  v15
  v16
  v17 =
    du_join'691''8314''45'left'8314'_892 v15 v16 v17
du_join'691''8314''45'left'8314'_892 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_join'691''8314''45'left'8314'_892 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
            v2
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 ->
          coe
            seq
            (coe v6)
            ( case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  case coe v4 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                v2
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                v2
                            )
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe
                            seq
                            (coe v12)
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                    v2
                                )
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v2
                _ -> MAlonzo.RTE.mazUnreachableError
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinʳ⁺-right⁺
d_join'691''8314''45'right'8314'_982 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_join'691''8314''45'right'8314'_982
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
  v15
  v16
  v17 =
    du_join'691''8314''45'right'8314'_982 v15 v16 v17
du_join'691''8314''45'right'8314'_982 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_join'691''8314''45'right'8314'_982 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 ->
      case coe v3 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
            v2
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 ->
          coe
            seq
            (coe v6)
            ( case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  case coe v4 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          case coe v2 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v20 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v20
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v21 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                    v21
                                )
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v22 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                v22
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          case coe v2 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v20 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                v20
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v21 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                    v21
                                )
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v22 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                v22
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe
                            seq
                            (coe v12)
                            ( case coe v2 of
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v20 ->
                                  coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                    ( coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                        v20
                                    )
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v21 ->
                                  case coe v21 of
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v28 ->
                                      coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                        v28
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v29 ->
                                      coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                        ( coe
                                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                            v29
                                        )
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v30 ->
                                      coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                        ( coe
                                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                            v30
                                        )
                                    _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v22 ->
                                  coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                    ( coe
                                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                        v22
                                    )
                                _ -> MAlonzo.RTE.mazUnreachableError
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v2
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v2
                _ -> MAlonzo.RTE.mazUnreachableError
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinˡ⁺⁻
d_join'737''8314''8315'_1196 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_join'737''8314''8315'_1196
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
  v14
  ~v15
  v16 =
    du_join'737''8314''8315'_1196 v14 v16
du_join'737''8314''8315'_1196 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_join'737''8314''8315'_1196 v0 v1 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 ->
      case coe v2 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_toSum_306
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v5 ->
          case coe v5 of
            MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
              case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_toSum_306
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_toSum_306
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  case coe v3 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe seq (coe v13) (coe du_'46'extendedlambda2_1278)
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          coe du_'46'extendedlambda1_1250
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe du_'46'extendedlambda0_1228
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
            MAlonzo.Code.Data.Fin.Base.C_suc_16 v7 ->
              coe (\v8 -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties..extendedlambda0
d_'46'extendedlambda0_1228 ::
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
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'46'extendedlambda0_1228
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
  v16 =
    du_'46'extendedlambda0_1228 v16
du_'46'extendedlambda0_1228 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'46'extendedlambda0_1228 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                v5
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v6 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                v6
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v7 ->
      case coe v7 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v14
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v15))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties..extendedlambda1
d_'46'extendedlambda1_1250 ::
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
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'46'extendedlambda1_1250
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
  v16 =
    du_'46'extendedlambda1_1250 v16
du_'46'extendedlambda1_1250 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'46'extendedlambda1_1250 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                v5
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v6 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                v6
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v7 ->
      case coe v7 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v14
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v15))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties..extendedlambda2
d_'46'extendedlambda2_1278 ::
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
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'46'extendedlambda2_1278
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
  ~v17
  ~v18
  ~v19
  ~v20
  v21 =
    du_'46'extendedlambda2_1278 v21
du_'46'extendedlambda2_1278 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'46'extendedlambda2_1278 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v5
                )
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v6 ->
      case coe v6 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v13
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v14
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    ( coe
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                        v15
                    )
                )
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v7 ->
      case coe v7 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    ( coe
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                        v14
                    )
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v15))
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.joinʳ⁺⁻
d_join'691''8314''8315'_1314 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_join'691''8314''8315'_1314
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
  v15
  v16 =
    du_join'691''8314''8315'_1314 v15 v16
du_join'691''8314''8315'_1314 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_join'691''8314''8315'_1314 v0 v1 =
  case coe v0 of
    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 ->
      case coe v2 of
        MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
          coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_toSum_306
        MAlonzo.Code.Data.Fin.Base.C_suc_16 v5 ->
          case coe v5 of
            MAlonzo.Code.Data.Fin.Base.C_zero_12 ->
              case coe v1 of
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                  case coe v3 of
                    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
                      case coe v14 of
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34 ->
                          coe du_'46'extendedlambda3_1346
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                          coe du_'46'extendedlambda4_1368
                        MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                          coe seq (coe v12) (coe du_'46'extendedlambda5_1396)
                        _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_toSum_306
                MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42 ->
                  coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.du_toSum_306
                _ -> MAlonzo.RTE.mazUnreachableError
            MAlonzo.Code.Data.Fin.Base.C_suc_16 v7 ->
              coe (\v8 -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties..extendedlambda3
d_'46'extendedlambda3_1346 ::
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
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'46'extendedlambda3_1346
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
  v16 =
    du_'46'extendedlambda3_1346 v16
du_'46'extendedlambda3_1346 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'46'extendedlambda3_1346 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                v5
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v6 ->
      case coe v6 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v14))
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v15
                )
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v7 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                v7
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties..extendedlambda4
d_'46'extendedlambda4_1368 ::
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
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'46'extendedlambda4_1368
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
  v16 =
    du_'46'extendedlambda4_1368 v16
du_'46'extendedlambda4_1368 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'46'extendedlambda4_1368 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                v5
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v6 ->
      case coe v6 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v14))
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    v15
                )
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v7 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                v7
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties..extendedlambda5
d_'46'extendedlambda5_1396 ::
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
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'46'extendedlambda5_1396
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
  ~v17
  ~v18
  ~v19
  ~v20
  v21 =
    du_'46'extendedlambda5_1396 v21
du_'46'extendedlambda5_1396 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'46'extendedlambda5_1396 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe
        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
        ( coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v5
                )
            )
        )
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v6 ->
      case coe v6 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v14))
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    ( coe
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                        v15
                    )
                )
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v7 ->
      case coe v7 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                    v13
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v14 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                    ( coe
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                        v14
                    )
                )
            )
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v15 ->
          coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            ( coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                ( coe
                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                    v15
                )
            )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.Val
d_Val_1420 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_1420 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.Val≈
d_Val'8776'_1422 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny
d_Val'8776'_1422 v0 =
  coe MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 (coe v0)

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.singleton⁺
d_singleton'8314'_1432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_singleton'8314'_1432
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
  v13 =
    du_singleton'8314'_1432 v13
du_singleton'8314'_1432 ::
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_singleton'8314'_1432 v0 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
    v0

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.singleton⁻
d_singleton'8315'_1450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
d_singleton'8315'_1450
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
  v13 =
    du_singleton'8315'_1450 v13
du_singleton'8315'_1450 ::
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_singleton'8315'_1450 v0 =
  case coe v0 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v5 ->
      coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.Any-insertWith-nothing
d_Any'45'insertWith'45'nothing_1564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  ( MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_Any'45'insertWith'45'nothing_1564
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  v6
  v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  v14
  v15
  ~v16 =
    du_Any'45'insertWith'45'nothing_1564 v3 v5 v6 v7 v13 v14 v15
du_Any'45'insertWith'45'nothing_1564 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_Any'45'insertWith'45'nothing_1564 v0 v1 v2 v3 v4 v5 v6 =
  case coe v4 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 v7 ->
      coe
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
        v6
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v7 v8 v10 v11 v12 v13 ->
      case coe v10 of
        MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v14 v15 ->
          case coe v5 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17 ->
              let v18 =
                    coe
                      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                      ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                          (coe v0)
                      )
                      v2
                      v14
               in coe
                    ( case coe v18 of
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v19 ->
                          coe
                            du_join'737''8314''45'left'8314'_498
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                (coe v0)
                                (coe v1)
                                (coe v2)
                                (coe v3)
                                (coe v11)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe v16)
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v19
                                        )
                                    )
                                )
                            )
                            (coe v13)
                            ( coe
                                du_Any'45'insertWith'45'nothing_1564
                                (coe v0)
                                (coe v1)
                                (coe v2)
                                (coe v3)
                                (coe v11)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe v16)
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v19
                                        )
                                    )
                                )
                                (coe v6)
                            )
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v20 ->
                          coe
                            MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_38
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v21 ->
                          coe
                            du_join'691''8314''45'right'8314'_982
                            ( coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                (coe v0)
                                (coe v1)
                                (coe v2)
                                (coe v3)
                                (coe v12)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v21
                                        )
                                    )
                                    (coe v17)
                                )
                            )
                            (coe v13)
                            ( coe
                                du_Any'45'insertWith'45'nothing_1564
                                (coe v0)
                                (coe v1)
                                (coe v2)
                                (coe v3)
                                (coe v12)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v21
                                        )
                                    )
                                    (coe v17)
                                )
                                (coe v6)
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    )
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.Any-insertWith-just
d_Any'45'insertWith'45'just_1694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_Any'45'insertWith'45'just_1694
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  v6
  v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  v14
  v15
  v16 =
    du_Any'45'insertWith'45'just_1694 v3 v5 v6 v7 v13 v14 v15 v16
du_Any'45'insertWith'45'just_1694 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_Any'45'insertWith'45'just_1694 v0 v1 v2 v3 v4 v5 v6 v7 =
  case coe v4 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
      case coe v11 of
        MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v15 v16 ->
          case coe v5 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18 ->
              let v19 =
                    coe
                      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                      ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                          (coe v0)
                      )
                      v2
                      v15
               in coe
                    ( case coe v7 of
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v24 ->
                          case coe v19 of
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v28 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v29 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                (coe v6 v15 v16 v29)
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v30 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v25 ->
                          case coe v19 of
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v28 ->
                              coe
                                du_join'737''8314''45'left'8314'_498
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v12)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v17)
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v28
                                            )
                                        )
                                    )
                                )
                                (coe v14)
                                ( coe
                                    du_Any'45'insertWith'45'just_1694
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v12)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v17)
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v28
                                            )
                                        )
                                    )
                                    (coe v6)
                                    (coe v25)
                                )
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v29 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v30 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v26 ->
                          case coe v19 of
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v28 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v29 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v30 ->
                              coe
                                du_join'691''8314''45'right'8314'_982
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v13)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v30
                                            )
                                        )
                                        (coe v18)
                                    )
                                )
                                (coe v14)
                                ( coe
                                    du_Any'45'insertWith'45'just_1694
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v13)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v30
                                            )
                                        )
                                        (coe v18)
                                    )
                                    (coe v6)
                                    (coe v26)
                                )
                            _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError
                    )
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.Any-insert-nothing
d_Any'45'insert'45'nothing_1986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  ( MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_Any'45'insert'45'nothing_1986
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
  v11
  v12
  ~v13
  ~v14 =
    du_Any'45'insert'45'nothing_1986 v3 v5 v9 v10 v11 v12
du_Any'45'insert'45'nothing_1986 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  ( MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_Any'45'insert'45'nothing_1986 v0 v1 v2 v3 v4 v5 v6 v7 =
  coe
    du_Any'45'insertWith'45'nothing_1564
    (coe v0)
    (coe v1)
    (coe v2)
    (coe (\v8 -> v3))
    (coe v4)
    (coe v5)
    v6

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.Any-insert-just
d_Any'45'insert'45'just_1996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_Any'45'insert'45'just_1996
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
  v11
  v12
  ~v13
  ~v14
  v15 =
    du_Any'45'insert'45'just_1996 v3 v5 v9 v10 v11 v12 v15
du_Any'45'insert'45'just_1996 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_Any'45'insert'45'just_1996 v0 v1 v2 v3 v4 v5 v6 =
  coe
    du_Any'45'insertWith'45'just_1694
    (coe v0)
    (coe v1)
    (coe v2)
    (coe (\v7 -> v3))
    (coe v4)
    (coe v5)
    (coe (\v7 v8 -> coe v6 v7))

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.insertWith⁺
d_insertWith'8314'_2020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_insertWith'8314'_2020
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  v6
  v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  v14
  v15
  ~v16 =
    du_insertWith'8314'_2020 v3 v5 v6 v7 v13 v14 v15
du_insertWith'8314'_2020 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_insertWith'8314'_2020 v0 v1 v2 v3 v4 v5 v6 =
  case coe v4 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v7 v8 v10 v11 v12 v13 ->
      case coe v10 of
        MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v14 v15 ->
          case coe v5 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17 ->
              case coe v6 of
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v22 ->
                  let v26 =
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                          ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                              (coe v0)
                          )
                          v2
                          v14
                   in coe
                        ( case coe v26 of
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v27 ->
                              coe
                                du_join'737''8314''45'here'8314'_408
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v11)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v16)
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v27
                                            )
                                        )
                                    )
                                )
                                (coe v13)
                                (coe v22)
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v28 ->
                              coe
                                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_38
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v29 ->
                              coe
                                du_join'691''8314''45'here'8314'_802
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v12)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v29
                                            )
                                        )
                                        (coe v17)
                                    )
                                )
                                (coe v13)
                                (coe v22)
                            _ -> MAlonzo.RTE.mazUnreachableError
                        )
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v23 ->
                  let v26 =
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                          ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                              (coe v0)
                          )
                          v2
                          v14
                   in coe
                        ( case coe v26 of
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v27 ->
                              coe
                                du_join'737''8314''45'left'8314'_498
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v11)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v16)
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v27
                                            )
                                        )
                                    )
                                )
                                (coe v13)
                                ( coe
                                    du_insertWith'8314'_2020
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v11)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v16)
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v27
                                            )
                                        )
                                    )
                                    (coe v23)
                                )
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v28 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                v23
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v29 ->
                              coe
                                du_join'691''8314''45'left'8314'_892
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v12)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v29
                                            )
                                        )
                                        (coe v17)
                                    )
                                )
                                (coe v13)
                                (coe v23)
                            _ -> MAlonzo.RTE.mazUnreachableError
                        )
                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v24 ->
                  let v26 =
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                          ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                              (coe v0)
                          )
                          v2
                          v14
                   in coe
                        ( case coe v26 of
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v27 ->
                              coe
                                du_join'737''8314''45'right'8314'_712
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v11)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v16)
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v27
                                            )
                                        )
                                    )
                                )
                                (coe v13)
                                (coe v24)
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v28 ->
                              coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                v24
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v29 ->
                              coe
                                du_join'691''8314''45'right'8314'_982
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v12)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v29
                                            )
                                        )
                                        (coe v17)
                                    )
                                )
                                (coe v13)
                                ( coe
                                    du_insertWith'8314'_2020
                                    (coe v0)
                                    (coe v1)
                                    (coe v2)
                                    (coe v3)
                                    (coe v12)
                                    ( coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                            ( coe
                                                MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                v29
                                            )
                                        )
                                        (coe v17)
                                    )
                                    (coe v24)
                                )
                            _ -> MAlonzo.RTE.mazUnreachableError
                        )
                _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.insert⁺
d_insert'8314'_2318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_insert'8314'_2318
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  v11
  v12 =
    du_insert'8314'_2318 v3 v5 v11 v12
du_insert'8314'_2318 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_insert'8314'_2318 v0 v1 v2 v3 v4 v5 v6 v7 =
  coe
    du_insertWith'8314'_2020
    (coe v0)
    (coe v1)
    (coe v2)
    (coe (\v8 -> v3))
    v4
    v5
    v6

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.insert⁻
d_insert'8315'_2356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_insert'8315'_2356
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  v8
  v9
  v10
  ~v11
  ~v12
  ~v13
  v14
  v15
  v16 =
    du_insert'8315'_2356 v3 v5 v8 v9 v10 v14 v15 v16
du_insert'8315'_2356 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_insert'8315'_2356 v0 v1 v2 v3 v4 v5 v6 v7 =
  case coe v5 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 v8 ->
      case coe v7 of
        MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v13 ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13)
        _ -> MAlonzo.RTE.mazUnreachableError
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v8 v9 v11 v12 v13 v14 ->
      case coe v11 of
        MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v15 v16 ->
          case coe v6 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18 ->
              let v19 =
                    coe
                      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                      ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                          (coe v0)
                      )
                      v3
                      v15
               in coe
                    ( case coe v19 of
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v20 ->
                          let v23 =
                                coe
                                  du_join'737''8314''8315'_1196
                                  ( coe
                                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_920
                                      v0
                                      v1
                                      v3
                                      v4
                                      v12
                                      ( coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe v17)
                                          ( coe
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                              ( coe
                                                  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                  v20
                                              )
                                          )
                                      )
                                  )
                                  v14
                                  v7
                           in coe
                                ( case coe v23 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v24 ->
                                      coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        ( coe
                                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                            ( coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                erased
                                                (coe v24)
                                            )
                                        )
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v24 ->
                                      case coe v24 of
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25 ->
                                          coe
                                            MAlonzo.Code.Data.Sum.Base.du_map'8322'_94
                                            ( \v26 ->
                                                coe
                                                  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                                  v26
                                            )
                                            ( coe
                                                du_insert'8315'_2356
                                                (coe v0)
                                                (coe v1)
                                                (coe v2)
                                                (coe v3)
                                                (coe v4)
                                                (coe v12)
                                                ( coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v17)
                                                    ( coe
                                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                                        ( coe
                                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                            v20
                                                        )
                                                    )
                                                )
                                                (coe v25)
                                            )
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25 ->
                                          coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                            ( coe
                                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                                ( coe
                                                    du_lookup'45'rebuild'45'accum_382
                                                    (coe v13)
                                                    (coe v25)
                                                    erased
                                                )
                                            )
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                                )
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v21 ->
                          case coe v7 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v27 ->
                              coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                (coe v2 v3 v15 v4 v21 v27)
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v28 ->
                              coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                    ( coe
                                        du_lookup'45'rebuild'45'accum_382
                                        (coe v12)
                                        (coe v28)
                                        erased
                                    )
                                )
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v29 ->
                              coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                ( coe
                                    MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                    ( coe
                                        du_lookup'45'rebuild'45'accum_382
                                        (coe v13)
                                        (coe v29)
                                        erased
                                    )
                                )
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v22 ->
                          let v23 =
                                coe
                                  du_join'691''8314''8315'_1314
                                  ( coe
                                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_920
                                      v0
                                      v1
                                      v3
                                      v4
                                      v13
                                      ( coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          ( coe
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                              ( coe
                                                  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                  v22
                                              )
                                          )
                                          (coe v18)
                                      )
                                  )
                                  v14
                                  v7
                           in coe
                                ( case coe v23 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v24 ->
                                      coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        ( coe
                                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                                            ( coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                erased
                                                (coe v24)
                                            )
                                        )
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v24 ->
                                      case coe v24 of
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25 ->
                                          coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                            ( coe
                                                MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                                                ( coe
                                                    du_lookup'45'rebuild'45'accum_382
                                                    (coe v12)
                                                    (coe v25)
                                                    erased
                                                )
                                            )
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25 ->
                                          coe
                                            MAlonzo.Code.Data.Sum.Base.du_map'8322'_94
                                            ( \v26 ->
                                                coe
                                                  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                                                  v26
                                            )
                                            ( coe
                                                du_insert'8315'_2356
                                                (coe v0)
                                                (coe v1)
                                                (coe v2)
                                                (coe v3)
                                                (coe v4)
                                                (coe v13)
                                                ( coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    ( coe
                                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                                        ( coe
                                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                            v22
                                                        )
                                                    )
                                                    (coe v18)
                                                )
                                                (coe v25)
                                            )
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                                )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    )
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.k′<p
d_k'8242''60'p_2464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny
d_k'8242''60'p_2464
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  ~v16
  ~v17
  ~v18
  ~v19
  ~v20
  v21
  ~v22
  ~v23
  ~v24
  ~v25
  v26
  ~v27 =
    du_k'8242''60'p_2464 v3 v5 v15 v21 v26
du_k'8242''60'p_2464 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_k'8242''60'p_2464 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
            )
            (coe v2)
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.k≉p
d_k'8777'p_2466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_k'8777'p_2466 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.p<k′
d_p'60'k'8242'_2574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny
d_p'60'k'8242'_2574
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  v14
  ~v15
  ~v16
  ~v17
  ~v18
  ~v19
  v20
  ~v21
  ~v22
  ~v23
  ~v24
  ~v25
  v26
  ~v27 =
    du_p'60'k'8242'_2574 v3 v5 v14 v20 v26
du_p'60'k'8242'_2574 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_p'60'k'8242'_2574 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            (coe v2)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
            )
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.k≉p
d_k'8777'p_2576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_k'8777'p_2576 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.p<k′
d_p'60'k'8242'_2656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny
d_p'60'k'8242'_2656
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  v14
  ~v15
  ~v16
  ~v17
  ~v18
  ~v19
  v20
  ~v21
  ~v22
  ~v23
  ~v24
  ~v25
  v26
  ~v27 =
    du_p'60'k'8242'_2656 v3 v5 v14 v20 v26
du_p'60'k'8242'_2656 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_p'60'k'8242'_2656 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            (coe v2)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
            )
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.k≉p
d_k'8777'p_2658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_k'8777'p_2658 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.k′<p
d_k'8242''60'p_2710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny
d_k'8242''60'p_2710
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  ~v13
  ~v14
  v15
  ~v16
  ~v17
  ~v18
  ~v19
  ~v20
  v21
  ~v22
  ~v23
  ~v24
  ~v25
  v26
  ~v27 =
    du_k'8242''60'p_2710 v3 v5 v15 v21 v26
du_k'8242''60'p_2710 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_k'8242''60'p_2710 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
            )
            (coe v2)
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._._.k≉p
d_k'8777'p_2712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  AgdaAny ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_k'8777'p_2712 = erased

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.lookup⁺
d_lookup'8314'_2726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_lookup'8314'_2726
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  ~v10
  v11
  v12
  v13
  v14 =
    du_lookup'8314'_2726 v3 v11 v12 v13 v14
du_lookup'8314'_2726 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_lookup'8314'_2726 v0 v1 v2 v3 v4 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v5 v6 v8 v9 v10 v11 ->
      case coe v8 of
        MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v12 v13 ->
          case coe v3 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15 ->
              let v16 =
                    coe
                      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                      ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                          (coe v0)
                      )
                      v12
                      v2
               in coe
                    ( case coe v16 of
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v17 ->
                          case coe v4 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v24 ->
                              coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v25 ->
                              coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v26 ->
                              coe
                                du_lookup'8314'_2726
                                (coe v0)
                                (coe v10)
                                (coe v2)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v17
                                        )
                                    )
                                    (coe v15)
                                )
                                (coe v26)
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v18 ->
                          case coe v4 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v24 ->
                              coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe v18)
                                    erased
                                )
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v25 ->
                              coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v26 ->
                              coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                            _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v19 ->
                          case coe v4 of
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216 v24 ->
                              coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232 v25 ->
                              coe
                                du_lookup'8314'_2726
                                (coe v0)
                                (coe v9)
                                (coe v2)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe v14)
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v19
                                        )
                                    )
                                )
                                (coe v25)
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248 v26 ->
                              coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                            _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError
                    )
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.p<k′
d_p'60'k'8242'_2842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
d_p'60'k'8242'_2842
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  ~v14
  v15
  ~v16
  ~v17
  ~v18
  ~v19
  ~v20
  ~v21
  ~v22
  v23
  ~v24
  ~v25 =
    du_p'60'k'8242'_2842 v3 v6 v13 v15 v23
du_p'60'k'8242'_2842 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_p'60'k'8242'_2842 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            (coe v1)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
            )
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.p<k′
d_p'60'k'8242'_2896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
d_p'60'k'8242'_2896
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  v6
  ~v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  ~v14
  v15
  ~v16
  ~v17
  ~v18
  ~v19
  ~v20
  ~v21
  ~v22
  v23
  ~v24
  ~v25 =
    du_p'60'k'8242'_2896 v3 v6 v13 v15 v23
du_p'60'k'8242'_2896 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_p'60'k'8242'_2896 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            (coe v1)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
            )
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.k′<p
d_k'8242''60'p_2926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
d_k'8242''60'p_2926
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  ~v6
  v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  ~v14
  ~v15
  v16
  ~v17
  ~v18
  ~v19
  ~v20
  ~v21
  ~v22
  v23
  ~v24
  ~v25 =
    du_k'8242''60'p_2926 v3 v7 v13 v16 v23
du_k'8242''60'p_2926 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_k'8242''60'p_2926 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
            )
            (coe v1)
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.k′<p
d_k'8242''60'p_2980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> ()) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
d_k'8242''60'p_2980
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  ~v6
  v7
  ~v8
  ~v9
  ~v10
  ~v11
  ~v12
  v13
  ~v14
  ~v15
  v16
  ~v17
  ~v18
  ~v19
  ~v20
  ~v21
  ~v22
  v23
  ~v24
  ~v25 =
    du_k'8242''60'p_2980 v3 v7 v13 v16 v23
du_k'8242''60'p_2980 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192 ->
  AgdaAny
du_k'8242''60'p_2980 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'91''60''93''45'injective_158
    ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
        ( coe
            du_lookup'45'bounded_330
            (coe v0)
            ( coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
            )
            (coe v1)
            (coe v3)
            (coe v4)
        )
    )

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.lookup⁻
d_lookup'8315'_3000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
d_lookup'8315'_3000
  ~v0
  ~v1
  ~v2
  v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  v9
  v10
  ~v11
  v12
  ~v13 =
    du_lookup'8315'_3000 v3 v9 v10 v12
du_lookup'8315'_3000 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.T_Any_192
du_lookup'8315'_3000 v0 v1 v2 v3 =
  case coe v1 of
    MAlonzo.Code.Data.Tree.AVL.Indexed.C_node_208 v4 v5 v7 v8 v9 v10 ->
      case coe v7 of
        MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v11 v12 ->
          case coe v3 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14 ->
              let v15 =
                    coe
                      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                      ( MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                          (coe v0)
                      )
                      v11
                      v2
               in coe
                    ( case coe v15 of
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v16 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_right_248
                            ( coe
                                du_lookup'8315'_3000
                                (coe v0)
                                (coe v9)
                                (coe v2)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v16
                                        )
                                    )
                                    (coe v14)
                                )
                            )
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v17 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_here_216
                            ( coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe v17)
                                erased
                            )
                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v18 ->
                          coe
                            MAlonzo.Code.Data.Tree.AVL.Indexed.Relation.Unary.Any.C_left_232
                            ( coe
                                du_lookup'8315'_3000
                                (coe v0)
                                (coe v8)
                                (coe v2)
                                ( coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe v13)
                                    ( coe
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                        ( coe
                                            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                            v18
                                        )
                                    )
                                )
                            )
                        _ -> MAlonzo.RTE.mazUnreachableError
                    )
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._..generalizedField-l
d_'46'generalizedField'45'l_3665657 ::
  T_GeneralizeTel_3665663 -> Maybe (Maybe AgdaAny)
d_'46'generalizedField'45'l_3665657 =
  MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._..generalizedField-u
d_'46'generalizedField'45'u_3665659 ::
  T_GeneralizeTel_3665663 -> Maybe (Maybe AgdaAny)
d_'46'generalizedField'45'u_3665659 =
  MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._..generalizedField-n
d_'46'generalizedField'45'n_3665661 ::
  T_GeneralizeTel_3665663 -> Integer
d_'46'generalizedField'45'n_3665661 =
  MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._._.GeneralizeTel
d_GeneralizeTel_3665663 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_GeneralizeTel_3665663
  = C_mkGeneralizeTel_3665665
      (Maybe (Maybe AgdaAny))
      (Maybe (Maybe AgdaAny))
      Integer

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._..generalizedField-l
d_'46'generalizedField'45'l_4238729 ::
  T_GeneralizeTel_4238735 -> Maybe (Maybe AgdaAny)
d_'46'generalizedField'45'l_4238729 =
  MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._..generalizedField-u
d_'46'generalizedField'45'u_4238731 ::
  T_GeneralizeTel_4238735 -> Maybe (Maybe AgdaAny)
d_'46'generalizedField'45'u_4238731 =
  MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._..generalizedField-n
d_'46'generalizedField'45'n_4238733 ::
  T_GeneralizeTel_4238735 -> Integer
d_'46'generalizedField'45'n_4238733 =
  MAlonzo.RTE.mazUnreachableError

-- Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties._.GeneralizeTel
d_GeneralizeTel_4238735 a0 a1 a2 a3 a4 a5 = ()
data T_GeneralizeTel_4238735
  = C_mkGeneralizeTel_4238737
      (Maybe (Maybe AgdaAny))
      (Maybe (Maybe AgdaAny))
      Integer
