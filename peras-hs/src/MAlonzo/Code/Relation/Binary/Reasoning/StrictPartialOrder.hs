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

module MAlonzo.Code.Relation.Binary.Reasoning.StrictPartialOrder where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
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

-- Relation.Binary.Reasoning.StrictPartialOrder._._IsRelatedTo_
d__IsRelatedTo__112 a0 a1 a2 a3 a4 a5 = ()

-- Relation.Binary.Reasoning.StrictPartialOrder._._∎
d__'8718'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_114 ~v0 ~v1 ~v2 v3 = du__'8718'_114 v3
du__'8718'_114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du__'8718'_114 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
            ( coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                (coe v1)
            )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.<-go
d_'60''45'go_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_116 ~v0 ~v1 ~v2 v3 = du_'60''45'go_116 v3
du_'60''45'go_116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'60''45'go_116 v0 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
    ( coe
        MAlonzo.Code.Relation.Binary.Structures.d_trans_306
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )
    ( coe
        MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )
    ( coe
        MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_'60''45''8804''45'trans_108
        ( coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_306
            ( coe
                MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                (coe v0)
            )
        )
        ( coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
            ( coe
                MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                (coe v0)
            )
        )
    )

-- Relation.Binary.Reasoning.StrictPartialOrder._.IsEquality
d_IsEquality_118 a0 a1 a2 a3 a4 a5 a6 = ()

-- Relation.Binary.Reasoning.StrictPartialOrder._.IsEquality?
d_IsEquality'63'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_120 ~v0 ~v1 ~v2 ~v3 = du_IsEquality'63'_120
du_IsEquality'63'_120 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsEquality'63'_120 v0 v1 v2 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
    v2

-- Relation.Binary.Reasoning.StrictPartialOrder._.IsStrict
d_IsStrict_122 a0 a1 a2 a3 a4 a5 a6 = ()

-- Relation.Binary.Reasoning.StrictPartialOrder._.IsStrict?
d_IsStrict'63'_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_124 ~v0 ~v1 ~v2 ~v3 = du_IsStrict'63'_124
du_IsStrict'63'_124 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsStrict'63'_124 v0 v1 v2 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
    v2

-- Relation.Binary.Reasoning.StrictPartialOrder._.begin_
d_begin__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_begin__126 ~v0 ~v1 ~v2 v3 = du_begin__126 v3
du_begin__126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_begin__126 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                \v2 v3 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_'60''8658''8804'_26
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    ( coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                        (coe v1)
                        (coe v2)
                    )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.begin-contradiction_
d_begin'45'contradiction__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny
d_begin'45'contradiction__128 ~v0 ~v1 ~v2 ~v3 =
  du_begin'45'contradiction__128
du_begin'45'contradiction__128 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny
du_begin'45'contradiction__128 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246

-- Relation.Binary.Reasoning.StrictPartialOrder._.begin_
d_begin__130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  AgdaAny
d_begin__130 ~v0 ~v1 ~v2 ~v3 = du_begin__130
du_begin__130 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  AgdaAny
du_begin__130 =
  let v0 =
        coe
          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
   in coe
        ( \v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
              (coe v0)
              v1
              v2
              v3
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.begin_
d_begin__132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  AgdaAny
d_begin__132 ~v0 ~v1 ~v2 ~v3 = du_begin__132
du_begin__132 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  AgdaAny
du_begin__132 =
  let v0 =
        coe
          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
   in coe
        ( \v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
              (coe v0)
              v1
              v2
              v3
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.eqRelation
d_eqRelation_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_134 ~v0 ~v1 ~v2 ~v3 = du_eqRelation_134
du_eqRelation_134 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_eqRelation_134 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238

-- Relation.Binary.Reasoning.StrictPartialOrder._.extractEquality
d_extractEquality_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  AgdaAny
d_extractEquality_138 ~v0 ~v1 ~v2 ~v3 = du_extractEquality_138
du_extractEquality_138 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  AgdaAny
du_extractEquality_138 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractEquality_234
    v2
    v3

-- Relation.Binary.Reasoning.StrictPartialOrder._.extractStrict
d_extractStrict_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  AgdaAny
d_extractStrict_140 ~v0 ~v1 ~v2 ~v3 = du_extractStrict_140
du_extractStrict_140 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  AgdaAny
du_extractStrict_140 v0 v1 v2 v3 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
    v2
    v3

-- Relation.Binary.Reasoning.StrictPartialOrder._.start
d_start_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_start_148 ~v0 ~v1 ~v2 v3 = du_start_148 v3
du_start_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_start_148 v0 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
    ( coe
        MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )
    ( \v1 v2 ->
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_'60''8658''8804'_26
    )

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-<
d_step'45''60'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_150 ~v0 ~v1 ~v2 v3 = du_step'45''60'_150 v3
du_step'45''60'_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''60'_150 v0 =
  let v1 =
        MAlonzo.Code.Relation.Binary.Structures.d_trans_306
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
                  ( coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                      (coe v0)
                  )
           in coe
                ( let v3 =
                        coe
                          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_'60''45''8804''45'trans_108
                          ( coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_306
                              ( coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                                  (coe v0)
                              )
                          )
                          ( coe
                              MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
                              ( coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                                  (coe v0)
                              )
                          )
                   in coe
                        ( coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                            ( coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                (coe v1)
                                (coe v2)
                                (coe v3)
                            )
                        )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≈
d_step'45''8776'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776'_152 ~v0 ~v1 ~v2 v3 = du_step'45''8776'_152 v3
du_step'45''8776'_152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776'_152 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
                  ( coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                      (coe v0)
                  )
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_372
                    ( coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe v1)
                        (coe v2)
                    )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≈-⟨
d_step'45''8776''45''10216'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776''45''10216'_154 ~v0 ~v1 ~v2 v3 =
  du_step'45''8776''45''10216'_154 v3
du_step'45''8776''45''10216'_154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776''45''10216'_154 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
                  ( coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                      (coe v0)
                  )
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                    ( coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe v1)
                        (coe v2)
                    )
                    ( coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        ( coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                            (coe v1)
                        )
                    )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≈-⟩
d_step'45''8776''45''10217'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776''45''10217'_156 ~v0 ~v1 ~v2 v3 =
  du_step'45''8776''45''10217'_156 v3
du_step'45''8776''45''10217'_156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776''45''10217'_156 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
                  ( coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                      (coe v0)
                  )
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                    ( coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe v1)
                        (coe v2)
                    )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≈˘
d_step'45''8776''728'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776''728'_158 ~v0 ~v1 ~v2 v3 =
  du_step'45''8776''728'_158 v3
du_step'45''8776''728'_158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776''728'_158 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
                  ( coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                      (coe v0)
                  )
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_374
                    ( coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe v1)
                        (coe v2)
                    )
                    ( coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        ( coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                            (coe v1)
                        )
                    )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≡
d_step'45''8801'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_160 ~v0 ~v1 ~v2 ~v3 = du_step'45''8801'_160
du_step'45''8801'_160 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801'_160 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
    (coe (\v0 v1 v2 v3 v4 -> v4))

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≡-∣
d_step'45''8801''45''8739'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 =
  du_step'45''8801''45''8739'_162 v6
du_step'45''8801''45''8739'_162 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_162 v0 = coe v0

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≡-⟨
d_step'45''8801''45''10216'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_164 ~v0 ~v1 ~v2 ~v3 =
  du_step'45''8801''45''10216'_164
du_step'45''8801''45''10216'_164 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''10216'_164 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
    (coe (\v0 v1 v2 v3 v4 -> v4))

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≡-⟩
d_step'45''8801''45''10217'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_166 ~v0 ~v1 ~v2 ~v3 =
  du_step'45''8801''45''10217'_166
du_step'45''8801''45''10217'_166 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''10217'_166 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
    (coe (\v0 v1 v2 v3 v4 -> v4))

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≡˘
d_step'45''8801''728'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_168 ~v0 ~v1 ~v2 ~v3 =
  du_step'45''8801''728'_168
du_step'45''8801''728'_168 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''728'_168 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
    (coe (\v0 v1 v2 v3 v4 -> v4))

-- Relation.Binary.Reasoning.StrictPartialOrder._.step-≤
d_step'45''8804'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_170 ~v0 ~v1 ~v2 v3 = du_step'45''8804'_170 v3
du_step'45''8804'_170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8804'_170 v0 =
  let v1 =
        coe
          MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
          ( coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
              (coe v0)
          )
   in coe
        ( let v2 =
                coe
                  MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_'8804''45''60''45'trans_126
                  ( let v2 =
                          coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_setoid_598
                            (coe v0)
                     in coe
                          ( coe
                              MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                              ( coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                  (coe v2)
                              )
                          )
                  )
                  ( coe
                      MAlonzo.Code.Relation.Binary.Structures.d_trans_306
                      ( coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                          (coe v0)
                      )
                  )
                  ( coe
                      MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
                      ( coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                          (coe v0)
                      )
                  )
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                    ( coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                        (coe v1)
                        (coe v2)
                    )
                )
        )

-- Relation.Binary.Reasoning.StrictPartialOrder._.stop
d_stop_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_172 ~v0 ~v1 ~v2 v3 = du_stop_172 v3
du_stop_172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_stop_172 v0 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
    ( coe
        MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )

-- Relation.Binary.Reasoning.StrictPartialOrder._.strictRelation
d_strictRelation_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_176 ~v0 ~v1 ~v2 ~v3 = du_strictRelation_176
du_strictRelation_176 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_strictRelation_176 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202

-- Relation.Binary.Reasoning.StrictPartialOrder._.≈-go
d_'8776''45'go_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_178 ~v0 ~v1 ~v2 v3 = du_'8776''45'go_178 v3
du_'8776''45'go_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8776''45'go_178 v0 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
    ( coe
        MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )
    ( coe
        MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )

-- Relation.Binary.Reasoning.StrictPartialOrder._.≡-go
d_'8801''45'go_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 =
  du_'8801''45'go_180 v8
du_'8801''45'go_180 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_180 v0 = coe v0

-- Relation.Binary.Reasoning.StrictPartialOrder._.≤-go
d_'8804''45'go_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_182 ~v0 ~v1 ~v2 v3 = du_'8804''45'go_182 v3
du_'8804''45'go_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8804''45'go_182 v0 =
  coe
    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
    ( coe
        MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_isPreorder'8322'_350
        ( coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)
        )
    )
    ( coe
        MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_'8804''45''60''45'trans_126
        ( let v1 =
                coe
                  MAlonzo.Code.Relation.Binary.Bundles.du_setoid_598
                  (coe v0)
           in coe
                ( coe
                    MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                    ( coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (coe v1)
                    )
                )
        )
        ( coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_306
            ( coe
                MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                (coe v0)
            )
        )
        ( coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
            ( coe
                MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
                (coe v0)
            )
        )
    )
