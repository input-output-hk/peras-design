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

module MAlonzo.Code.Peras.Chain where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Haskell.Prelude
import qualified MAlonzo.Code.Haskell.Prim
import qualified MAlonzo.Code.Haskell.Prim.Bool
import qualified MAlonzo.Code.Haskell.Prim.Eq
import qualified MAlonzo.Code.Haskell.Prim.Foldable
import qualified MAlonzo.Code.Haskell.Prim.List
import qualified MAlonzo.Code.Haskell.Prim.Maybe
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.Crypto
import qualified MAlonzo.Code.Peras.Numbering
import qualified MAlonzo.Code.Peras.Params
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

import qualified Peras.Chain as G

-- Peras.Chain.Vote
d_Vote_4 = ()
type T_Vote_4 = G.Vote
pattern C_MkVote_26 a0 a1 a2 a3 a4 = G.MkVote a0 a1 a2 a3 a4
check_MkVote_26 ::
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  Integer ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14
    MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  T_Vote_4
check_MkVote_26 = G.MkVote
cover_Vote_4 :: G.Vote -> ()
cover_Vote_4 x =
  case x of
    G.MkVote _ _ _ _ _ -> ()

-- Peras.Chain.Vote.votingRound
d_votingRound_16 ::
  T_Vote_4 -> MAlonzo.Code.Peras.Numbering.T_RoundNumber_24
d_votingRound_16 v0 =
  case coe v0 of
    C_MkVote_26 v1 v2 v3 v4 v5 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain.Vote.creatorId
d_creatorId_18 :: T_Vote_4 -> Integer
d_creatorId_18 v0 =
  case coe v0 of
    C_MkVote_26 v1 v2 v3 v4 v5 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain.Vote.proofM
d_proofM_20 ::
  T_Vote_4 -> MAlonzo.Code.Peras.Crypto.T_MembershipProof_42
d_proofM_20 v0 =
  case coe v0 of
    C_MkVote_26 v1 v2 v3 v4 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain.Vote.blockHash
d_blockHash_22 ::
  T_Vote_4 ->
  MAlonzo.Code.Peras.Crypto.T_Hash_14
    MAlonzo.Code.Peras.Block.T_Block_62
d_blockHash_22 v0 =
  case coe v0 of
    C_MkVote_26 v1 v2 v3 v4 v5 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain.Vote.signature
d_signature_24 ::
  T_Vote_4 -> MAlonzo.Code.Peras.Crypto.T_Signature_70
d_signature_24 v0 =
  case coe v0 of
    C_MkVote_26 v1 v2 v3 v4 v5 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain.iVoteEq
d_iVoteEq_28 :: MAlonzo.Code.Haskell.Prim.Eq.T_Eq_8
d_iVoteEq_28 =
  coe
    MAlonzo.Code.Haskell.Prim.Eq.C_Eq'46'constructor_7
    ( coe
        ( \v0 v1 ->
            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
              ( coe
                  eqInt
                  ( coe
                      MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                      (coe d_votingRound_16 (coe v0))
                  )
                  ( coe
                      MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                      (coe d_votingRound_16 (coe v1))
                  )
              )
              ( coe
                  MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                  ( coe
                      eqInt
                      (coe d_creatorId_18 (coe v0))
                      (coe d_creatorId_18 (coe v1))
                  )
                  ( coe
                      MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                      ( coe
                          MAlonzo.Code.Peras.Crypto.d_eqBS_8
                          (MAlonzo.Code.Peras.Crypto.d_proofM_46 (coe d_proofM_20 (coe v0)))
                          (MAlonzo.Code.Peras.Crypto.d_proofM_46 (coe d_proofM_20 (coe v1)))
                      )
                      ( coe
                          MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                          ( coe
                              MAlonzo.Code.Peras.Crypto.d_eqBS_8
                              ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                  (coe d_blockHash_22 (coe v0))
                              )
                              ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                  (coe d_blockHash_22 (coe v1))
                              )
                          )
                          ( coe
                              MAlonzo.Code.Peras.Crypto.d_eqBS_8
                              ( MAlonzo.Code.Peras.Crypto.d_bytesS_74
                                  (coe d_signature_24 (coe v0))
                              )
                              ( MAlonzo.Code.Peras.Crypto.d_bytesS_74
                                  (coe d_signature_24 (coe v1))
                              )
                          )
                      )
                  )
              )
        )
    )

-- Peras.Chain._.ValidVote
d_ValidVote_42 ::
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  (T_Vote_4 -> MAlonzo.Code.Peras.Crypto.T_Signature_70 -> ()) ->
  T_Vote_4 ->
  ()
d_ValidVote_42 = erased

-- Peras.Chain._∻_
d__'8763'__46 a0 a1 = ()
data T__'8763'__46 = C_Equivocation_52

-- Peras.Chain.Chain
d_Chain_54 :: ()
d_Chain_54 = erased

-- Peras.Chain._⪯_
d__'10927'__56 a0 a1 = ()
newtype T__'10927'__56
  = C_Prefix_64 [MAlonzo.Code.Peras.Block.T_Block_62]

-- Peras.Chain.prune
d_prune_66 ::
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_prune_66 v0 =
  case coe v0 of
    MAlonzo.Code.Peras.Numbering.C_MkSlotNumber_16 v1 ->
      coe
        MAlonzo.Code.Data.List.Base.du_filter_740
        ( coe
            ( \v2 ->
                MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2672
                  (coe MAlonzo.Code.Peras.Block.d_slotNumber''_108 (coe v2))
                  (coe v1)
            )
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain._.nonZero
d_nonZero_100 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZero_100 ~v0 v1 = du_nonZero_100 v1
du_nonZero_100 ::
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_nonZero_100 v0 =
  coe MAlonzo.Code.Peras.Params.d_T'45'nonZero_40 (coe v0)

-- Peras.Chain._._PointsInto_
d__PointsInto__106 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ()
d__PointsInto__106 = erased

-- Peras.Chain._._PointsInto?_
d__PointsInto'63'__116 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__PointsInto'63'__116 v0 ~v1 v2 = du__PointsInto'63'__116 v0 v2
du__PointsInto'63'__116 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__PointsInto'63'__116 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
    ( coe
        ( \v2 ->
            coe
              MAlonzo.Code.Peras.Block.d__'8799''45'BlockHash__114
              (MAlonzo.Code.Peras.Block.d_blockRef_74 (coe v1))
              (coe MAlonzo.Code.Peras.Crypto.d_hash_40 v0 v2)
        )
    )

-- Peras.Chain._.StartOfRound
d_StartOfRound_122 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  ()
d_StartOfRound_122 = erased

-- Peras.Chain._.v-round
d_v'45'round_130 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24
d_v'45'round_130 ~v0 v1 v2 ~v3 = du_v'45'round_130 v1 v2
du_v'45'round_130 ::
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24
du_v'45'round_130 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Peras.Numbering.C_MkSlotNumber_16 v2 ->
      coe
        MAlonzo.Code.Peras.Numbering.C_MkRoundNumber_32
        ( coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__314
            (coe v2)
            (coe MAlonzo.Code.Peras.Params.d_T_24 (coe v0))
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain._.∥_∥_
d_'8741'_'8741'__134 ::
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  Integer
d_'8741'_'8741'__134 v0 v1 v2 v3 =
  coe
    addInt
    (coe MAlonzo.Code.Data.List.Base.du_length_304 v2)
    ( coe
        mulInt
        ( coe
            MAlonzo.Code.Data.List.Base.du_length_304
            ( coe
                MAlonzo.Code.Data.List.Base.du_filter_740
                (coe (\v4 -> coe du__PointsInto'63'__116 v0 v4 v2))
                (coe v3)
            )
        )
        (coe MAlonzo.Code.Peras.Params.d_B_36 (coe v1))
    )

-- Peras.Chain._.ValidChain
d_ValidChain_158 a0 a1 a2 a3 a4 = ()
data T_ValidChain_158
  = C_Genesis_160
  | C_Cons_168 AgdaAny AgdaAny T_ValidChain_158

-- Peras.Chain._.tip
d_tip_172 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  T_ValidChain_158 ->
  MAlonzo.Code.Peras.Block.T_Block_62
d_tip_172 v0 ~v1 ~v2 v3 v4 v5 = du_tip_172 v0 v3 v4 v5
du_tip_172 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  T_ValidChain_158 ->
  MAlonzo.Code.Peras.Block.T_Block_62
du_tip_172 v0 v1 v2 v3 =
  case coe v3 of
    C_Genesis_160 -> coe v0
    C_Cons_168 v7 v8 v10 ->
      case coe v2 of
        (:) v11 v12 ->
          case coe v12 of
            (:) v13 v14 ->
              case coe v11 of
                MAlonzo.Code.Peras.Block.C_MkBlock_110 v15 v16 v17 v18 v19 v20 v21 ->
                  coe
                    MAlonzo.Code.Peras.Block.C_MkBlock_110
                    (coe v15)
                    (coe v16)
                    (coe MAlonzo.Code.Peras.Crypto.d_hash_40 v1 v13)
                    (coe v18)
                    (coe v19)
                    (coe v20)
                    (coe v21)
                _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.Chain.foldl1Maybe
d_foldl1Maybe_180 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_foldl1Maybe_180 ~v0 v1 v2 = du_foldl1Maybe_180 v1 v2
du_foldl1Maybe_180 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
du_foldl1Maybe_180 v0 v1 =
  coe
    MAlonzo.Code.Haskell.Prim.Foldable.du_foldl_170
    ( coe
        MAlonzo.Code.Haskell.Prim.Foldable.C_DefaultFoldable'46'constructor_4805
        ( \v2 v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Haskell.Prim.Foldable.du_foldMapList_408
              v4
              v5
              v6
        )
    )
    ( coe
        ( \v2 v3 ->
            coe
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18
              ( coe
                  MAlonzo.Code.Haskell.Prim.du_case_of__58
                  (coe v2)
                  ( coe
                      ( \v4 v5 ->
                          case coe v4 of
                            MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 -> coe v3
                            MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v6 -> coe v0 v6 v3
                            _ -> MAlonzo.RTE.mazUnreachableError
                      )
                  )
              )
        )
    )
    (coe MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16)
    (coe v1)

-- Peras.Chain.prefix
d_prefix_194 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_prefix_194 v0 v1 v2 =
  let v3 = coe MAlonzo.Code.Haskell.Prelude.du_reverse_28 v0
   in coe
        ( case coe v1 of
            (:) v4 v5 ->
              case coe v2 of
                (:) v6 v7 ->
                  coe
                    MAlonzo.Code.Haskell.Prim.du_if_then_else__68
                    ( coe
                        MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                        ( coe
                            eqInt
                            ( coe
                                MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                (coe MAlonzo.Code.Peras.Block.d_slotNumber_94 (coe v4))
                            )
                            ( coe
                                MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                (coe MAlonzo.Code.Peras.Block.d_slotNumber_94 (coe v6))
                            )
                        )
                        ( coe
                            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                            ( coe
                                eqInt
                                (coe MAlonzo.Code.Peras.Block.d_creatorId_96 (coe v4))
                                (coe MAlonzo.Code.Peras.Block.d_creatorId_96 (coe v6))
                            )
                            ( coe
                                MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                ( coe
                                    MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                    ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                        (coe MAlonzo.Code.Peras.Block.d_parentBlock_98 (coe v4))
                                    )
                                    ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                        (coe MAlonzo.Code.Peras.Block.d_parentBlock_98 (coe v6))
                                    )
                                )
                                ( coe
                                    MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                    ( coe
                                        MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                        ( MAlonzo.Code.Peras.Crypto.d_proofL_60
                                            ( coe
                                                MAlonzo.Code.Peras.Block.d_leadershipProof_102
                                                (coe v4)
                                            )
                                        )
                                        ( MAlonzo.Code.Peras.Crypto.d_proofL_60
                                            ( coe
                                                MAlonzo.Code.Peras.Block.d_leadershipProof_102
                                                (coe v6)
                                            )
                                        )
                                    )
                                    ( coe
                                        MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                        ( coe
                                            MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                                            ( \v8 ->
                                                coe
                                                  MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                                                  ( \v9 ->
                                                      MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                                        ( coe
                                                            eqInt
                                                            ( coe
                                                                MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                                                                ( coe
                                                                    MAlonzo.Code.Peras.Block.d_round_72
                                                                    (coe v8)
                                                                )
                                                            )
                                                            ( coe
                                                                MAlonzo.Code.Peras.Numbering.d_getRoundNumber_28
                                                                ( coe
                                                                    MAlonzo.Code.Peras.Block.d_round_72
                                                                    (coe v9)
                                                                )
                                                            )
                                                        )
                                                        ( coe
                                                            MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                                            ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                                                ( coe
                                                                    MAlonzo.Code.Peras.Block.d_blockRef_74
                                                                    (coe v8)
                                                                )
                                                            )
                                                            ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                                                ( coe
                                                                    MAlonzo.Code.Peras.Block.d_blockRef_74
                                                                    (coe v9)
                                                                )
                                                            )
                                                        )
                                                  )
                                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                  (MAlonzo.Code.Peras.Block.d_certificate_100 (coe v6))
                                            )
                                            ( coe
                                                MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_48
                                                (\v8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                (MAlonzo.Code.Peras.Block.d_certificate_100 (coe v6))
                                            )
                                            (MAlonzo.Code.Peras.Block.d_certificate_100 (coe v4))
                                        )
                                        ( coe
                                            MAlonzo.Code.Haskell.Prim.Bool.d__'38''38'__6
                                            ( coe
                                                MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                                ( MAlonzo.Code.Peras.Crypto.d_bytesS_74
                                                    ( coe
                                                        MAlonzo.Code.Peras.Block.d_signature_104
                                                        (coe v4)
                                                    )
                                                )
                                                ( MAlonzo.Code.Peras.Crypto.d_bytesS_74
                                                    ( coe
                                                        MAlonzo.Code.Peras.Block.d_signature_104
                                                        (coe v6)
                                                    )
                                                )
                                            )
                                            ( coe
                                                MAlonzo.Code.Peras.Crypto.d_eqBS_8
                                                ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                                    ( coe
                                                        MAlonzo.Code.Peras.Block.d_bodyHash_106
                                                        (coe v4)
                                                    )
                                                )
                                                ( MAlonzo.Code.Peras.Crypto.d_hashBytes_20
                                                    ( coe
                                                        MAlonzo.Code.Peras.Block.d_bodyHash_106
                                                        (coe v6)
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                    ( coe
                        ( \v8 ->
                            d_prefix_194
                              ( coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe v4)
                                  (coe v0)
                              )
                              (coe v5)
                              (coe v7)
                        )
                    )
                    (coe (\v8 -> coe MAlonzo.Code.Haskell.Prelude.du_reverse_28 v0))
                _ -> coe v3
            _ -> coe v3
        )

-- Peras.Chain.commonPrefix
d_commonPrefix_208 ::
  [[MAlonzo.Code.Peras.Block.T_Block_62]] ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_commonPrefix_208 v0 =
  coe
    MAlonzo.Code.Haskell.Prim.du_case_of__58
    (coe d_listPrefix_216 (coe v0))
    ( coe
        ( \v1 v2 ->
            case coe v1 of
              MAlonzo.Code.Haskell.Prim.Maybe.C_Nothing_16 ->
                coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
              MAlonzo.Code.Haskell.Prim.Maybe.C_Just_18 v3 ->
                coe MAlonzo.Code.Haskell.Prelude.du_reverse_28 v3
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )

-- Peras.Chain._.listPrefix
d_listPrefix_216 ::
  [[MAlonzo.Code.Peras.Block.T_Block_62]] ->
  MAlonzo.Code.Haskell.Prim.Maybe.T_Maybe_10
d_listPrefix_216 v0 =
  coe
    du_foldl1Maybe_180
    ( coe
        d_prefix_194
        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    )
    ( coe
        MAlonzo.Code.Haskell.Prim.List.du_map_6
        (coe MAlonzo.Code.Haskell.Prelude.du_reverse_28)
        (coe v0)
    )
