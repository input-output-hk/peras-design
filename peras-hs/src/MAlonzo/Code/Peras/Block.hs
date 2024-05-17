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

module MAlonzo.Code.Peras.Block where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Peras.Crypto
import qualified MAlonzo.Code.Peras.Numbering
import qualified MAlonzo.Code.Relation.Binary.Bundles
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

import qualified Peras.Block as G

-- Peras.Block.PartyId
d_PartyId_4 :: ()
d_PartyId_4 = erased

-- Peras.Block.PartyIdO
d_PartyIdO_6 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_PartyIdO_6 =
  coe
    MAlonzo.Code.Data.Nat.Properties.d_'60''45'strictTotalOrder_2922

-- Peras.Block.Party
d_Party_8 = ()
type T_Party_8 = G.Party
pattern C_MkParty_18 a0 a1 = G.MkParty a0 a1
check_MkParty_18 ::
  Integer ->
  MAlonzo.Code.Peras.Crypto.T_VerificationKey_84 ->
  T_Party_8
check_MkParty_18 = G.MkParty
cover_Party_8 :: G.Party -> ()
cover_Party_8 x =
  case x of
    G.MkParty _ _ -> ()

-- Peras.Block.Party.pid
d_pid_14 :: T_Party_8 -> Integer
d_pid_14 v0 =
  case coe v0 of
    C_MkParty_18 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Party.pkey
d_pkey_16 ::
  T_Party_8 -> MAlonzo.Code.Peras.Crypto.T_VerificationKey_84
d_pkey_16 v0 =
  case coe v0 of
    C_MkParty_18 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.iPartyEq
d_iPartyEq_20 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iPartyEq_20 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              (coe eqInt (coe d_pid_14 (coe v0)) (coe d_pid_14 (coe v1)))
              ( coe
                  MAlonzo.Code.Peras.Crypto.d_eqBS_8
                  (MAlonzo.Code.Peras.Crypto.d_keyV_88 (coe d_pkey_16 (coe v0)))
                  (MAlonzo.Code.Peras.Crypto.d_keyV_88 (coe d_pkey_16 (coe v1)))
              )
        )
    )

-- Peras.Block.Honesty
d_Honesty_26 a0 = ()
data T_Honesty_26 = C_Honest_30 | C_Corrupt_34

-- Peras.Block.PartyTup
d_PartyTup_36 :: ()
d_PartyTup_36 = erased

-- Peras.Block.Parties
d_Parties_40 :: ()
d_Parties_40 = erased

-- Peras.Block.Honest≢Corrupt
d_Honest'8802'Corrupt_50 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Block.Honest\8802Corrupt"

-- Peras.Block.isHonest
d_isHonest_54 :: Integer -> T_Honesty_26 -> Bool
d_isHonest_54 ~v0 v1 = du_isHonest_54 v1
du_isHonest_54 :: T_Honesty_26 -> Bool
du_isHonest_54 v0 =
  case coe v0 of
    C_Honest_30 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
    C_Corrupt_34 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Tx
d_Tx_60 :: ()
d_Tx_60 = erased

-- Peras.Block.Block
d_Block_62 = ()
type T_Block_62 = G.Block
pattern C_MkBlock_110 a0 a1 a2 a3 a4 a5 a6 = G.MkBlock a0 a1 a2 a3 a4 a5 a6
check_MkBlock_110 ::
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  Integer ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14 T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10 () T_Certificate_66 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14
    ( MAlonzo.Code.Agda.Builtin.List.T_List_10
        ()
        MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
    ) ->
  T_Block_62
check_MkBlock_110 = G.MkBlock
cover_Block_62 :: G.Block -> ()
cover_Block_62 x =
  case x of
    G.MkBlock _ _ _ _ _ _ _ -> ()

-- Peras.Block.BlockBody
d_BlockBody_64 = ()
type T_BlockBody_64 = G.BlockBody
pattern C_MkBlockBody_124 a0 a1 = G.MkBlockBody a0 a1
check_MkBlockBody_124 ::
  MAlonzo.Code.Peras.Crypto.T_Hash_14
    ( MAlonzo.Code.Agda.Builtin.List.T_List_10
        ()
        MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
    ) ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10
    ()
    MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  T_BlockBody_64
check_MkBlockBody_124 = G.MkBlockBody
cover_BlockBody_64 :: G.BlockBody -> ()
cover_BlockBody_64 x =
  case x of
    G.MkBlockBody _ _ -> ()

-- Peras.Block.Certificate
d_Certificate_66 = ()
type T_Certificate_66 = G.Certificate
pattern C_MkCertificate_78 a0 a1 = G.MkCertificate a0 a1
check_MkCertificate_78 ::
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14 T_Block_62 ->
  T_Certificate_66
check_MkCertificate_78 = G.MkCertificate
cover_Certificate_66 :: G.Certificate -> ()
cover_Certificate_66 x =
  case x of
    G.MkCertificate _ _ -> ()

-- Peras.Block.Certificate.round
d_round_72 ::
  T_Certificate_66 -> MAlonzo.Code.Peras.Numbering.T_RoundNumber_24
d_round_72 v0 =
  case coe v0 of
    C_MkCertificate_78 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Certificate.blockRef
d_blockRef_74 ::
  T_Certificate_66 -> MAlonzo.Code.Peras.Crypto.T_Hash_14 T_Block_62
d_blockRef_74 v0 =
  case coe v0 of
    C_MkCertificate_78 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Certificate.roundNumber
d_roundNumber_76 :: T_Certificate_66 -> Integer
d_roundNumber_76 v0 =
  coe
    MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
    (coe d_round_72 (coe v0))

-- Peras.Block.Block.slotNumber
d_slotNumber_94 ::
  T_Block_62 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_slotNumber_94 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.creatorId
d_creatorId_96 :: T_Block_62 -> Integer
d_creatorId_96 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.parentBlock
d_parentBlock_98 ::
  T_Block_62 -> MAlonzo.Code.Peras.Crypto.T_Hash_14 T_Block_62
d_parentBlock_98 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.certificate
d_certificate_100 :: T_Block_62 -> Maybe T_Certificate_66
d_certificate_100 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.leadershipProof
d_leadershipProof_102 ::
  T_Block_62 -> MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56
d_leadershipProof_102 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.signature
d_signature_104 ::
  T_Block_62 -> MAlonzo.Code.Peras.Crypto.T_Signature_70
d_signature_104 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.bodyHash
d_bodyHash_106 ::
  T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
d_bodyHash_106 v0 =
  case coe v0 of
    C_MkBlock_110 v1 v2 v3 v4 v5 v6 v7 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.Block.slotNumber'
d_slotNumber''_108 :: T_Block_62 -> Integer
d_slotNumber''_108 v0 =
  coe
    MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
    (coe d_slotNumber_94 (coe v0))

-- Peras.Block._≟-Block_
d__'8799''45'Block__112 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Block._\8799-Block_"

-- Peras.Block._≟-BlockHash_
d__'8799''45'BlockHash__114 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.Block._\8799-BlockHash_"

-- Peras.Block.BlockBody.blockHash
d_blockHash_120 ::
  T_BlockBody_64 ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
d_blockHash_120 v0 =
  case coe v0 of
    C_MkBlockBody_124 v1 v2 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.BlockBody.payload
d_payload_122 ::
  T_BlockBody_64 -> [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
d_payload_122 v0 =
  case coe v0 of
    C_MkBlockBody_124 v1 v2 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Block.HonestBlock
d_HonestBlock_126 a0 = ()
data T_HonestBlock_126 = C_HonestParty_134 Integer T_Honesty_26

-- Peras.Block.iMaybeEq
d_iMaybeEq_140 ::
  () ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iMaybeEq_140 ~v0 v1 = du_iMaybeEq_140 v1
du_iMaybeEq_140 ::
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8 ->
  MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
du_iMaybeEq_140 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v1 v2 ->
            coe
              MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
              ( \v3 ->
                  coe
                    MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                    (coe MAlonzo.Code.Haskell.Prim.Eq.d__'61''61'__14 v0 v3)
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    v2
              )
              ( coe
                  MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                  (\v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  v2
              )
              v1
        )
    )

-- Peras.Block.iCertificateEq
d_iCertificateEq_154 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iCertificateEq_154 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  eqInt
                  ( coe
                      MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                      (coe d_round_72 (coe v0))
                  )
                  ( coe
                      MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                      (coe d_round_72 (coe v1))
                  )
              )
              ( coe
                  MAlonzo.Code.Peras.Crypto.d_eqBS_8
                  ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                      (coe d_blockRef_74 (coe v0))
                  )
                  ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                      (coe d_blockRef_74 (coe v1))
                  )
              )
        )
    )

-- Peras.Block.iBlockEq
d_iBlockEq_160 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iBlockEq_160 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  eqInt
                  ( coe
                      MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                      (coe d_slotNumber_94 (coe v0))
                  )
                  ( coe
                      MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                      (coe d_slotNumber_94 (coe v1))
                  )
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                  ( coe
                      eqInt
                      (coe d_creatorId_96 (coe v0))
                      (coe d_creatorId_96 (coe v1))
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                      ( coe
                          MAlonzo.Code.Peras.Crypto.d_eqBS_8
                          ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                              (coe d_parentBlock_98 (coe v0))
                          )
                          ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                              (coe d_parentBlock_98 (coe v1))
                          )
                      )
                      ( coe
                          MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                          ( coe
                              MAlonzo.Code.Peras.Crypto.d_eqBS_8
                              ( MAlonzo.Code.Peras.Crypto.d_proofL_60
                                  (coe d_leadershipProof_102 (coe v0))
                              )
                              ( MAlonzo.Code.Peras.Crypto.d_proofL_60
                                  (coe d_leadershipProof_102 (coe v1))
                              )
                          )
                          ( coe
                              MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                              ( coe
                                  MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                                  ( \v2 ->
                                      coe
                                        MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                                        ( \v3 ->
                                            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                              ( coe
                                                  eqInt
                                                  ( coe
                                                      MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                                                      (coe d_round_72 (coe v2))
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                                                      (coe d_round_72 (coe v3))
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                                  ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                                      (coe d_blockRef_74 (coe v2))
                                                  )
                                                  ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                                      (coe d_blockRef_74 (coe v3))
                                                  )
                                              )
                                        )
                                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                        (d_certificate_100 (coe v1))
                                  )
                                  ( coe
                                      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                                      (\v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                      (d_certificate_100 (coe v1))
                                  )
                                  (d_certificate_100 (coe v0))
                              )
                              ( coe
                                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                      ( MAlonzo.Code.Peras.Crypto.d_bytesS_74
                                          (coe d_signature_104 (coe v0))
                                      )
                                      ( MAlonzo.Code.Peras.Crypto.d_bytesS_74
                                          (coe d_signature_104 (coe v1))
                                      )
                                  )
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                      ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                          (coe d_bodyHash_106 (coe v0))
                                      )
                                      ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                          (coe d_bodyHash_106 (coe v1))
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
        )
    )

-- Peras.Block.hashBlock
d_hashBlock_166 :: MAlonzo.Code.Peras.Crypto.T_Hashable_34
d_hashBlock_166 =
  coe
    MAlonzo.Code.Peras.Crypto.C_Hashable'46'constructor_173
    ( coe
        ( \v0 ->
            coe
              MAlonzo.Code.Peras.Crypto.C_MkHash_22
              ( coe
                  MAlonzo.Code.Peras.Crypto.d_bytesS_74
                  (coe d_signature_104 (coe v0))
              )
        )
    )
