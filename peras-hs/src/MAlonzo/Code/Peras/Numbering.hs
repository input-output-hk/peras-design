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

module MAlonzo.Code.Peras.Numbering where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Haskell.Prim.Eq
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

import qualified Peras.Numbering as G

-- Peras.Numbering.SlotNumber
d_SlotNumber_4 = ()
type T_SlotNumber_4 = G.SlotNumber
pattern C_MkSlotNumber_16 a0 = G.MkSlotNumber a0
check_MkSlotNumber_16 :: Integer -> T_SlotNumber_4
check_MkSlotNumber_16 = G.MkSlotNumber
cover_SlotNumber_4 :: G.SlotNumber -> ()
cover_SlotNumber_4 x =
  case x of
    G.MkSlotNumber _ -> ()

-- Peras.Numbering.SlotNumber.getSlotNumber
d_getSlotNumber_8 :: T_SlotNumber_4 -> Integer
d_getSlotNumber_8 v0 =
  case coe v0 of
    C_MkSlotNumber_16 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Numbering.SlotNumber.next
d_next_10 :: T_SlotNumber_4 -> T_SlotNumber_4
d_next_10 v0 =
  coe
    C_MkSlotNumber_16
    (coe addInt (coe (1 :: Integer)) (coe d_getSlotNumber_8 (coe v0)))

-- Peras.Numbering.SlotNumber._earlierBy_
d__earlierBy__12 :: T_SlotNumber_4 -> Integer -> T_SlotNumber_4
d__earlierBy__12 v0 v1 =
  coe
    C_MkSlotNumber_16
    ( coe
        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
        (d_getSlotNumber_8 (coe v0))
        v1
    )

-- Peras.Numbering.iSlotNumberEq
d_iSlotNumberEq_18 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iSlotNumberEq_18 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            eqInt
              (coe d_getSlotNumber_8 (coe v0))
              (coe d_getSlotNumber_8 (coe v1))
        )
    )

-- Peras.Numbering.RoundNumber
d_RoundNumber_24 = ()
type T_RoundNumber_24 = G.RoundNumber
pattern C_MkRoundNumber_32 a0 = G.MkRoundNumber a0
check_MkRoundNumber_32 :: Integer -> T_RoundNumber_24
check_MkRoundNumber_32 = G.MkRoundNumber
cover_RoundNumber_24 :: G.RoundNumber -> ()
cover_RoundNumber_24 x =
  case x of
    G.MkRoundNumber _ -> ()

-- Peras.Numbering.RoundNumber.getRoundNumber
d_getRoundNumber_28 :: T_RoundNumber_24 -> Integer
d_getRoundNumber_28 v0 =
  case coe v0 of
    C_MkRoundNumber_32 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Numbering.RoundNumber.prev
d_prev_30 :: T_RoundNumber_24 -> T_RoundNumber_24
d_prev_30 v0 =
  coe
    C_MkRoundNumber_32
    ( coe
        MAlonzo.Code.Data.Nat.Base.d_pred_192
        (coe d_getRoundNumber_28 (coe v0))
    )

-- Peras.Numbering.iRoundNumberEq
d_iRoundNumberEq_34 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iRoundNumberEq_34 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            eqInt
              (coe d_getRoundNumber_28 (coe v0))
              (coe d_getRoundNumber_28 (coe v1))
        )
    )

-- Peras.Numbering._≟-RoundNumber_
d__'8799''45'RoundNumber__40 ::
  T_RoundNumber_24 ->
  T_RoundNumber_24 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'RoundNumber__40 v0 v1 =
  case coe v0 of
    C_MkRoundNumber_32 v2 ->
      case coe v1 of
        C_MkRoundNumber_32 v3 ->
          let v4 =
                MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                  (coe v2)
                  (coe v3)
           in coe
                ( case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6 ->
                      if coe v5
                        then
                          coe
                            seq
                            (coe v6)
                            ( coe
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                (coe v5)
                                ( coe
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                    erased
                                )
                            )
                        else
                          coe
                            seq
                            (coe v6)
                            ( coe
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                (coe v5)
                                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                            )
                    _ -> MAlonzo.RTE.mazUnreachableError
                )
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Numbering.roundToSlot
d_roundToSlot_62 :: Integer -> T_RoundNumber_24 -> T_SlotNumber_4
d_roundToSlot_62 v0 v1 =
  case coe v1 of
    C_MkRoundNumber_32 v2 ->
      coe C_MkSlotNumber_16 (coe mulInt (coe v2) (coe v0))
    _ -> MAlonzo.RTE.mazUnreachableError
