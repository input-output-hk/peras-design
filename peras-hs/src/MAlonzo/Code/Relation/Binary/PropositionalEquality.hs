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

module MAlonzo.Code.Relation.Binary.PropositionalEquality where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Function.Dependent.Bundles
import qualified MAlonzo.Code.Function.Indexed.Relation.Binary.Equality
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
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

-- Relation.Binary.PropositionalEquality._→-setoid_
d__'8594''45'setoid__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d__'8594''45'setoid__26 ~v0 ~v1 ~v2 ~v3 = du__'8594''45'setoid__26
du__'8594''45'setoid__26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du__'8594''45'setoid__26 =
  coe
    MAlonzo.Code.Function.Indexed.Relation.Binary.Equality.du_'8801''45'setoid_18
    ( coe
        MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du_indexedSetoid_106
        ( coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
        )
    )

-- Relation.Binary.PropositionalEquality._≗_
d__'8791'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  ()
d__'8791'__36 = erased

-- Relation.Binary.PropositionalEquality.:→-to-Π
d_'58''8594''45'to'45'Π_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
d_'58''8594''45'to'45'Π_48 ~v0 ~v1 ~v2 ~v3 v4 v5 =
  du_'58''8594''45'to'45'Π_48 v4 v5
du_'58''8594''45'to'45'Π_48 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
du_'58''8594''45'to'45'Π_48 v0 v1 =
  coe
    MAlonzo.Code.Function.Dependent.Bundles.C_Func'46'constructor_677
    (coe v1)
    (\v2 v3 v4 -> coe du_'46'extendedlambda0_54 (coe v0) (coe v1) v2)

-- Relation.Binary.PropositionalEquality..extendedlambda0
d_'46'extendedlambda0_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny
d_'46'extendedlambda0_54 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 =
  du_'46'extendedlambda0_54 v4 v5 v6
du_'46'extendedlambda0_54 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny
du_'46'extendedlambda0_54 v0 v1 v2 =
  coe
    MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
    ( MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isEquivalence_38
        (coe v0)
    )
    v2
    (coe v1 v2)

-- Relation.Binary.PropositionalEquality.→-to-⟶
d_'8594''45'to'45''10230'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
d_'8594''45'to'45''10230'_60 ~v0 ~v1 ~v2 ~v3 v4 =
  du_'8594''45'to'45''10230'_60 v4
du_'8594''45'to'45''10230'_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
du_'8594''45'to'45''10230'_60 v0 =
  coe
    du_'58''8594''45'to'45'Π_48
    ( coe
        MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_IndexedSetoid'46'constructor_445
        ( coe
            MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du_isIndexedEquivalence_32
            ( coe
                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                (coe v0)
            )
        )
    )

-- Relation.Binary.PropositionalEquality.naturality
d_naturality_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_naturality_76 = erased

-- Relation.Binary.PropositionalEquality.cong-≡id
d_cong'45''8801'id_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45''8801'id_94 = erased

-- Relation.Binary.PropositionalEquality._.fx≡x
d_fx'8801'x_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fx'8801'x_106 = erased

-- Relation.Binary.PropositionalEquality._.f²x≡x
d_f'178'x'8801'x_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'178'x'8801'x_108 = erased

-- Relation.Binary.PropositionalEquality._.≡-≟-identity
d_'8801''45''8799''45'identity_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45''8799''45'identity_128 = erased

-- Relation.Binary.PropositionalEquality._.≢-≟-identity
d_'8802''45''8799''45'identity_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  AgdaAny ->
  AgdaAny ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''45''8799''45'identity_134 = erased

-- Relation.Binary.PropositionalEquality.Reveal_·_is_
d_Reveal_'183'_is__152 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Reveal_'183'_is__152 = C_'91'_'93'_168

-- Relation.Binary.PropositionalEquality.Reveal_·_is_.eq
d_eq_166 ::
  T_Reveal_'183'_is__152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_166 = erased

-- Relation.Binary.PropositionalEquality.inspect
d_inspect_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_Reveal_'183'_is__152
d_inspect_180 = erased

-- Relation.Binary.PropositionalEquality.isPropositional
d_isPropositional_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_isPropositional_186 = erased