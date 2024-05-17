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

module MAlonzo.Code.Peras.QQCD.Crypto where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Haskell.Prim.Tuple
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

import qualified Data.Binary as B
import qualified Data.ByteString as BS (ByteString, concat, empty)
import qualified Data.ByteString.Lazy as LBS (toStrict)
import qualified Data.Hashable as H

primHash = LBS.toStrict . B.encode . H.hash

-- Peras.QCD.Crypto.ByteString
type T_ByteString_6 = BS.ByteString
d_ByteString_6 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.QCD.Crypto.ByteString"

-- Peras.QCD.Crypto.emptyBS
d_emptyBS_8 :: T_ByteString_6
d_emptyBS_8 = BS.empty

-- Peras.QCD.Crypto.concatBS
d_concatBS_10 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_ByteString_6 ->
  T_ByteString_6
d_concatBS_10 = BS.concat

-- Peras.QCD.Crypto.eqBS
d_eqBS_12 :: T_ByteString_6 -> T_ByteString_6 -> Bool
d_eqBS_12 = (==)

-- Peras.QCD.Crypto.Hash
d_Hash_16 a0 = ()
newtype T_Hash_16 = C_MakeHash_24 T_ByteString_6

-- Peras.QCD.Crypto.Hash.hashBytes
d_hashBytes_22 :: T_Hash_16 -> T_ByteString_6
d_hashBytes_22 v0 =
  case coe v0 of
    C_MakeHash_24 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Crypto.iHashEq
d_iHashEq_26 :: () -> MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iHashEq_26 ~v0 = du_iHashEq_26
du_iHashEq_26 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
du_iHashEq_26 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            coe d_eqBS_12 (d_hashBytes_22 (coe v0)) (d_hashBytes_22 (coe v1))
        )
    )

-- Peras.QCD.Crypto.Hashable
d_Hashable_34 a0 = ()
newtype T_Hashable_34
  = C_Hashable'46'constructor_187 (AgdaAny -> T_Hash_16)

-- Peras.QCD.Crypto.Hashable.hash
d_hash_40 :: T_Hashable_34 -> AgdaAny -> T_Hash_16
d_hash_40 v0 =
  case coe v0 of
    C_Hashable'46'constructor_187 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.QCD.Crypto.primHashUnit
d_primHashUnit_42 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> T_ByteString_6
d_primHashUnit_42 = primHash

-- Peras.QCD.Crypto.primHashNat
d_primHashNat_44 :: Integer -> T_ByteString_6
d_primHashNat_44 = primHash

-- Peras.QCD.Crypto.primHashBytes
d_primHashBytes_46 :: T_ByteString_6 -> T_ByteString_6
d_primHashBytes_46 = primHash

-- Peras.QCD.Crypto.iUnitHashable
d_iUnitHashable_48 :: T_Hashable_34
d_iUnitHashable_48 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Haskell.Prim.du__'36'__48
              (coe C_MakeHash_24)
              ( coe
                  d_primHashUnit_42
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              )
        )
    )

-- Peras.QCD.Crypto.iByteStringHashable
d_iByteStringHashable_50 :: T_Hashable_34
d_iByteStringHashable_50 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe C_MakeHash_24)
        (coe d_primHashBytes_46)
    )

-- Peras.QCD.Crypto.iHashHashable
d_iHashHashable_52 :: () -> T_Hashable_34
d_iHashHashable_52 ~v0 = du_iHashHashable_52
du_iHashHashable_52 :: T_Hashable_34
du_iHashHashable_52 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe C_MakeHash_24)
            (coe d_primHashBytes_46)
        )
        (coe (\v0 -> d_hashBytes_22 (coe v0)))
    )

-- Peras.QCD.Crypto.iNatHashable
d_iNatHashable_54 :: T_Hashable_34
d_iNatHashable_54 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe C_MakeHash_24)
        (coe d_primHashNat_44)
    )

-- Peras.QCD.Crypto.iListHashable
d_iListHashable_58 :: () -> T_Hashable_34 -> T_Hashable_34
d_iListHashable_58 ~v0 v1 = du_iListHashable_58 v1
du_iListHashable_58 :: T_Hashable_34 -> T_Hashable_34
du_iListHashable_58 v0 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        MAlonzo.Code.Haskell.Prim.du__'8728'__28
        (coe C_MakeHash_24)
        ( coe
            MAlonzo.Code.Haskell.Prim.du__'8728'__28
            (coe d_primHashBytes_46)
            ( coe
                MAlonzo.Code.Haskell.Prim.du__'8728'__28
                (coe d_concatBS_10)
                ( coe
                    MAlonzo.Code.Haskell.Prim.List.du_map_6
                    (coe (\v1 -> d_hashBytes_22 (coe d_hash_40 v0 v1)))
                )
            )
        )
    )

-- Peras.QCD.Crypto.iPairHashable
d_iPairHashable_68 ::
  () -> () -> T_Hashable_34 -> T_Hashable_34 -> T_Hashable_34
d_iPairHashable_68 ~v0 ~v1 v2 v3 = du_iPairHashable_68 v2 v3
du_iPairHashable_68 ::
  T_Hashable_34 -> T_Hashable_34 -> T_Hashable_34
du_iPairHashable_68 v0 v1 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        ( \v2 ->
            case coe v2 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'__24 v3 v4 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du__'36'__48
                  ( coe
                      MAlonzo.Code.Haskell.Prim.du__'8728'__28
                      (coe C_MakeHash_24)
                      (coe d_primHashBytes_46)
                  )
                  ( coe
                      d_concatBS_10
                      ( coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe d_hashBytes_22 (coe d_hash_40 v0 v3))
                          ( coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe d_hashBytes_22 (coe d_hash_40 v1 v4))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          )
                      )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Peras.QCD.Crypto.iTripletHashable
d_iTripletHashable_88 ::
  () ->
  () ->
  () ->
  T_Hashable_34 ->
  T_Hashable_34 ->
  T_Hashable_34 ->
  T_Hashable_34
d_iTripletHashable_88 ~v0 ~v1 ~v2 v3 v4 v5 =
  du_iTripletHashable_88 v3 v4 v5
du_iTripletHashable_88 ::
  T_Hashable_34 -> T_Hashable_34 -> T_Hashable_34 -> T_Hashable_34
du_iTripletHashable_88 v0 v1 v2 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        ( \v3 ->
            case coe v3 of
              MAlonzo.Code.Haskell.Prim.Tuple.C__'44'_'44'__40 v4 v5 v6 ->
                coe
                  MAlonzo.Code.Haskell.Prim.du__'36'__48
                  ( coe
                      MAlonzo.Code.Haskell.Prim.du__'8728'__28
                      (coe C_MakeHash_24)
                      (coe d_primHashBytes_46)
                  )
                  ( coe
                      d_concatBS_10
                      ( coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe d_hashBytes_22 (coe d_hash_40 v0 v4))
                          ( coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe d_hashBytes_22 (coe d_hash_40 v1 v5))
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe d_hashBytes_22 (coe d_hash_40 v2 v6))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              )
                          )
                      )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Peras.QCD.Crypto.castHash
d_castHash_108 :: () -> () -> T_Hash_16 -> T_Hash_16
d_castHash_108 ~v0 ~v1 = du_castHash_108
du_castHash_108 :: T_Hash_16 -> T_Hash_16
du_castHash_108 =
  coe
    MAlonzo.Code.Haskell.Prim.du__'8728'__28
    (coe C_MakeHash_24)
    (coe (\v0 -> d_hashBytes_22 (coe v0)))

-- Peras.QCD.Crypto.iMaybeHashable
d_iMaybeHashable_112 :: () -> T_Hashable_34 -> T_Hashable_34
d_iMaybeHashable_112 ~v0 v1 = du_iMaybeHashable_112 v1
du_iMaybeHashable_112 :: T_Hashable_34 -> T_Hashable_34
du_iMaybeHashable_112 v0 =
  coe
    C_Hashable'46'constructor_187
    ( coe
        ( \v1 ->
            case coe v1 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe
                  du_castHash_108
                  ( coe
                      MAlonzo.Code.Haskell.Prim.du__'36'__48
                      (coe C_MakeHash_24)
                      ( coe
                          d_primHashUnit_42
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      )
                  )
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v2 ->
                coe
                  du_castHash_108
                  ( coe
                      MAlonzo.Code.Haskell.Prim.du__'36'__48
                      ( coe
                          MAlonzo.Code.Haskell.Prim.du__'8728'__28
                          (coe C_MakeHash_24)
                          (coe d_primHashBytes_46)
                      )
                      ( coe
                          d_concatBS_10
                          ( coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              ( coe
                                  d_hashBytes_22
                                  ( coe
                                      MAlonzo.Code.Haskell.Prim.du__'36'__48
                                      (coe C_MakeHash_24)
                                      ( coe
                                          d_primHashUnit_42
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                      )
                                  )
                              )
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe d_hashBytes_22 (coe d_hash_40 v0 v2))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              )
                          )
                      )
                  )
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
