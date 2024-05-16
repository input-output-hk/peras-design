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

module MAlonzo.Code.Axiom.UniquenessOfIdentityProofs where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
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

-- Axiom.UniquenessOfIdentityProofs.UIP
d_UIP_8 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_UIP_8 = erased

-- Axiom.UniquenessOfIdentityProofs.Constant⇒UIP.≡-canonical
d_'8801''45'canonical_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'canonical_36 = erased

-- Axiom.UniquenessOfIdentityProofs.Constant⇒UIP.≡-irrelevant
d_'8801''45'irrelevant_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'irrelevant_38 = erased

-- Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-normalise
d_'8801''45'normalise_56 ::
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
d_'8801''45'normalise_56 = erased

-- Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-normalise-constant
d_'8801''45'normalise'45'constant_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'normalise'45'constant_92 = erased

-- Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-irrelevant
d_'8801''45'irrelevant_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ( AgdaAny ->
    AgdaAny ->
    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
  ) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'irrelevant_124 = erased
