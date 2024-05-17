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

module MAlonzo.Code.Axiom.Extensionality.Propositional where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
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

-- Axiom.Extensionality.Propositional.Extensionality
d_Extensionality_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ()
d_Extensionality_10 = erased

-- Axiom.Extensionality.Propositional.ExtensionalityImplicit
d_ExtensionalityImplicit_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ()
d_ExtensionalityImplicit_32 = erased

-- Axiom.Extensionality.Propositional.lower-extensionality
d_lower'45'extensionality_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ( () ->
    (AgdaAny -> ()) ->
    (AgdaAny -> AgdaAny) ->
    (AgdaAny -> AgdaAny) ->
    (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'45'extensionality_62 = erased

-- Axiom.Extensionality.Propositional.∀-extensionality
d_'8704''45'extensionality_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ( () ->
    (AgdaAny -> ()) ->
    (AgdaAny -> AgdaAny) ->
    (AgdaAny -> AgdaAny) ->
    (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8704''45'extensionality_90 = erased

-- Axiom.Extensionality.Propositional.implicit-extensionality
d_implicit'45'extensionality_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ( () ->
    (AgdaAny -> ()) ->
    (AgdaAny -> AgdaAny) ->
    (AgdaAny -> AgdaAny) ->
    (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
  ) ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_implicit'45'extensionality_116 = erased
