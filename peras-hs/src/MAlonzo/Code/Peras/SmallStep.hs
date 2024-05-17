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

module MAlonzo.Code.Peras.SmallStep where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Extrema
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Map
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.Chain
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

-- Peras.SmallStep._.argmax
d_argmax_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Integer) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny
d_argmax_6 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.List.Extrema.du_argmax_136
    (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2696)
    v2

-- Peras.SmallStep.M.Map
d_Map_12 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_12 = erased

-- Peras.SmallStep.M.insert
d_insert_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insert_26 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)

-- Peras.SmallStep.M.lookup
d_lookup_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Integer ->
  Maybe AgdaAny
d_lookup_38 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_208
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)

-- Peras.SmallStep._._⊆_
d__'8838'__60 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ()
d__'8838'__60 = erased

-- Peras.SmallStep.Message
d_Message_62 = ()
data T_Message_62
  = C_BlockMsg_64 MAlonzo.Code.Peras.Block.T_Block_62
  | C_VoteMsg_66 MAlonzo.Code.Peras.Chain.T_Vote_4

-- Peras.SmallStep.Message-injective
d_Message'45'injective_72 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Message'45'injective_72 = erased

-- Peras.SmallStep.Message-injective′
d_Message'45'injective'8242'_78 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_Message'45'injective'8242'_78 = erased

-- Peras.SmallStep.Delay
d_Delay_80 :: ()
d_Delay_80 = erased

-- Peras.SmallStep.Envelope
d_Envelope_82 = ()
data T_Envelope_82
  = C_'10629'_'44'_'44'_'44'_'10630'_100
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T_Message_62
      MAlonzo.Code.Data.Fin.Base.T_Fin_10

-- Peras.SmallStep.Envelope.partyId
d_partyId_92 :: T_Envelope_82 -> Integer
d_partyId_92 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Envelope.honesty
d_honesty_94 ::
  T_Envelope_82 -> MAlonzo.Code.Peras.Block.T_Honesty_26
d_honesty_94 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Envelope.message
d_message_96 :: T_Envelope_82 -> T_Message_62
d_message_96 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Envelope.delay
d_delay_98 :: T_Envelope_82 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_delay_98 v0 =
  case coe v0 of
    C_'10629'_'44'_'44'_'44'_'10630'_100 v1 v2 v3 v4 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.⦅⦆-injective
d_'10629''10630''45'injective_106 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10629''10630''45'injective_106 = erased

-- Peras.SmallStep.⦅⦆-injective₃
d_'10629''10630''45'injective'8323'_112 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10629''10630''45'injective'8323'_112 = erased

-- Peras.SmallStep.⦅⦆-injective′
d_'10629''10630''45'injective'8242'_118 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'10629''10630''45'injective'8242'_118 = erased

-- Peras.SmallStep.⦅⦆-injective₃′
d_'10629''10630''45'injective'8323''8242'_124 ::
  T_Envelope_82 ->
  T_Envelope_82 ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'10629''10630''45'injective'8323''8242'_124 = erased

-- Peras.SmallStep._≐_
d__'8784'__126 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ()
d__'8784'__126 = erased

-- Peras.SmallStep._.getCert
d_getCert_178 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  Maybe MAlonzo.Code.Peras.Block.T_Certificate_66
d_getCert_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 =
  du_getCert_178 v9 v10
du_getCert_178 ::
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  Maybe MAlonzo.Code.Peras.Block.T_Certificate_66
du_getCert_178 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Base.du_head_608
    ( coe
        MAlonzo.Code.Data.List.Base.du_filter_740
        ( coe
            ( \v2 ->
                MAlonzo.Code.Peras.Numbering.d__'8799''45'RoundNumber__40
                  (coe MAlonzo.Code.Peras.Block.d_round_72 (coe v2))
                  (coe v0)
            )
        )
        (coe v1)
    )

-- Peras.SmallStep._.latestCert
d_latestCert_184 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
d_latestCert_184 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 =
  du_latestCert_184 v1
du_latestCert_184 ::
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66] ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
du_latestCert_184 v0 =
  coe
    MAlonzo.Code.Data.List.Extrema.du_argmax_136
    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalOrder_2696
    MAlonzo.Code.Peras.Block.d_roundNumber_76
    v0

-- Peras.SmallStep._.IsTreeType
d_IsTreeType_202
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T_IsTreeType_202
  = C_IsTreeType'46'constructor_14275
      ( AgdaAny ->
        MAlonzo.Code.Peras.Block.T_Block_62 ->
        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
      )
      ( AgdaAny ->
        MAlonzo.Code.Peras.Chain.T_Vote_4 ->
        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
      )
      ( AgdaAny ->
        MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        MAlonzo.Code.Peras.Chain.T_ValidChain_158
      )
      ( [MAlonzo.Code.Peras.Block.T_Block_62] ->
        AgdaAny ->
        MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        MAlonzo.Code.Peras.Chain.T_ValidChain_158 ->
        ( MAlonzo.Code.Peras.Block.T_Block_62 ->
          MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
          MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
        ) ->
        MAlonzo.Code.Data.Nat.Base.T__'8804'__22
      )
      ( AgdaAny ->
        MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        MAlonzo.Code.Peras.Block.T_Block_62 ->
        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
      )
      ( AgdaAny ->
        MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
      )

-- Peras.SmallStep._.IsTreeType.allBlocksUpTo
d_allBlocksUpTo_302 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Peras.Block.T_Block_62 -> AgdaAny) ->
  (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62]) ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    AgdaAny ->
    [MAlonzo.Code.Peras.Block.T_Block_62]
  ) ->
  (AgdaAny -> MAlonzo.Code.Peras.Chain.T_Vote_4 -> AgdaAny) ->
  (AgdaAny -> [MAlonzo.Code.Peras.Chain.T_Vote_4]) ->
  (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Certificate_66]) ->
  T_IsTreeType_202 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_allBlocksUpTo_302
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
  v12
  ~v13
  ~v14
  ~v15
  ~v16
  ~v17
  v18
  v19 =
    du_allBlocksUpTo_302 v12 v18 v19
du_allBlocksUpTo_302 ::
  (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62]) ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
du_allBlocksUpTo_302 v0 v1 v2 =
  coe
    MAlonzo.Code.Data.List.Base.du_filter_740
    ( coe
        ( \v3 ->
            MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2672
              (coe MAlonzo.Code.Peras.Block.d_slotNumber''_108 (coe v3))
              (coe MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8 (coe v1))
        )
    )
    (coe v0 v2)

-- Peras.SmallStep._.IsTreeType.instantiated
d_instantiated_310 ::
  T_IsTreeType_202 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_instantiated_310 = erased

-- Peras.SmallStep._.IsTreeType.extendable
d_extendable_316 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendable_316 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_14275 v2 v3 v4 v5 v6 v7 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.extendable-votes
d_extendable'45'votes_322 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendable'45'votes_322 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_14275 v2 v3 v4 v5 v6 v7 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.valid
d_valid_328 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Chain.T_ValidChain_158
d_valid_328 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_14275 v2 v3 v4 v5 v6 v7 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.optimal
d_optimal_340 ::
  T_IsTreeType_202 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Chain.T_ValidChain_158 ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_optimal_340 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_14275 v2 v3 v4 v5 v6 v7 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.self-contained
d_self'45'contained_346 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_self'45'contained_346 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_14275 v2 v3 v4 v5 v6 v7 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.valid-votes
d_valid'45'votes_350 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid'45'votes_350 v0 =
  case coe v0 of
    C_IsTreeType'46'constructor_14275 v2 v3 v4 v5 v6 v7 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.IsTreeType.unique-votes
d_unique'45'votes_358 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'45'votes_358 = erased

-- Peras.SmallStep._.IsTreeType.no-equivocations
d_no'45'equivocations_368 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'equivocations_368 = erased

-- Peras.SmallStep._.IsTreeType.non-quorum
d_non'45'quorum_374 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_non'45'quorum_374 = erased

-- Peras.SmallStep._.IsTreeType.quorum
d_quorum_382 ::
  T_IsTreeType_202 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_quorum_382 = erased

-- Peras.SmallStep._.TreeType
d_TreeType_386 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_TreeType_386
  = C_TreeType'46'constructor_18637
      AgdaAny
      (AgdaAny -> MAlonzo.Code.Peras.Block.T_Block_62 -> AgdaAny)
      (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62])
      ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
        AgdaAny ->
        [MAlonzo.Code.Peras.Block.T_Block_62]
      )
      (AgdaAny -> MAlonzo.Code.Peras.Chain.T_Vote_4 -> AgdaAny)
      (AgdaAny -> [MAlonzo.Code.Peras.Chain.T_Vote_4])
      (AgdaAny -> [MAlonzo.Code.Peras.Block.T_Certificate_66])
      T_IsTreeType_202

-- Peras.SmallStep._.TreeType.tree₀
d_tree'8320'_406 :: T_TreeType_386 -> AgdaAny
d_tree'8320'_406 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.extendTree
d_extendTree_408 ::
  T_TreeType_386 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  AgdaAny
d_extendTree_408 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.allBlocks
d_allBlocks_410 ::
  T_TreeType_386 -> AgdaAny -> [MAlonzo.Code.Peras.Block.T_Block_62]
d_allBlocks_410 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.bestChain
d_bestChain_412 ::
  T_TreeType_386 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Block_62]
d_bestChain_412 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.addVote
d_addVote_414 ::
  T_TreeType_386 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  AgdaAny
d_addVote_414 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.votes
d_votes_416 ::
  T_TreeType_386 -> AgdaAny -> [MAlonzo.Code.Peras.Chain.T_Vote_4]
d_votes_416 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.certs
d_certs_418 ::
  T_TreeType_386 ->
  AgdaAny ->
  [MAlonzo.Code.Peras.Block.T_Certificate_66]
d_certs_418 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.is-TreeType
d_is'45'TreeType_420 :: T_TreeType_386 -> T_IsTreeType_202
d_is'45'TreeType_420 v0 =
  case coe v0 of
    C_TreeType'46'constructor_18637 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.TreeType.tipBest
d_tipBest_422 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62
d_tipBest_422 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 v10 v11 v12 =
  du_tipBest_422 v0 v6 v10 v11 v12
du_tipBest_422 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  T_TreeType_386 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62
du_tipBest_422 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Peras.Chain.du_tip_172
    (coe v0)
    (coe v1)
    (coe d_bestChain_412 v2 v3 v4)
    (coe d_valid_328 (d_is'45'TreeType_420 (coe v2)) v4 v3)

-- Peras.SmallStep._.TreeType.latestCertOnChain
d_latestCertOnChain_432 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
d_latestCertOnChain_432
  ~v0
  v1
  ~v2
  ~v3
  ~v4
  ~v5
  ~v6
  ~v7
  ~v8
  ~v9
  v10
  v11
  v12 =
    du_latestCertOnChain_432 v1 v10 v11 v12
du_latestCertOnChain_432 ::
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  T_TreeType_386 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
du_latestCertOnChain_432 v0 v1 v2 v3 =
  coe
    du_latestCert_184
    v0
    ( coe
        MAlonzo.Code.Data.List.Base.du_catMaybes_60
        ( coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe (\v4 -> MAlonzo.Code.Peras.Block.d_certificate_100 (coe v4)))
            (coe d_bestChain_412 v1 v2 v3)
        )
    )

-- Peras.SmallStep._.TreeType.latestCertSeen
d_latestCertSeen_436 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
d_latestCertSeen_436 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 =
  du_latestCertSeen_436 v1 v10 v11
du_latestCertSeen_436 ::
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  T_TreeType_386 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Certificate_66
du_latestCertSeen_436 v0 v1 v2 =
  coe du_latestCert_184 v0 (coe d_certs_418 v1 v2)

-- Peras.SmallStep._.LocalState
d_LocalState_442 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
newtype T_LocalState_442 = C_'10218'_'10219'_452 AgdaAny

-- Peras.SmallStep._.LocalState.tree
d_tree_450 :: T_LocalState_442 -> AgdaAny
d_tree_450 v0 =
  case coe v0 of
    C_'10218'_'10219'_452 v1 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._.⟪⟫-injective
d_'10218''10219''45'injective_462 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  T_LocalState_442 ->
  T_LocalState_442 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'injective_462 = erased

-- Peras.SmallStep._._.Stateˡ
d_State'737'_480 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ()
d_State'737'_480 = erased

-- Peras.SmallStep._._._[_]→_
d__'91'_'93''8594'__482
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17 =
    ()
data T__'91'_'93''8594'__482
  = C_VoteReceived_488
  | C_BlockReceived_494

-- Peras.SmallStep._._.VoteInRound
d_VoteInRound_496
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T_VoteInRound_496
  = C_Regular_506 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  | C_AfterCooldown_518
      Integer
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22

-- Peras.SmallStep._._.Stateᵍ
d_State'7501'_520 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 =
  ()
data T_State'7501'_520
  = C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
      MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
      MAlonzo.Code.Data.Tree.AVL.T_Tree_254
      [T_Envelope_82]
      [T_Message_62]
      AgdaAny

-- Peras.SmallStep._._.Stateᵍ.clock
d_clock_532 ::
  T_State'7501'_520 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_532 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v1 v2 v3 v4 v5 -> coe v1
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.stateMap
d_stateMap_534 ::
  T_State'7501'_520 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_534 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v1 v2 v3 v4 v5 -> coe v2
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.messages
d_messages_536 :: T_State'7501'_520 -> [T_Envelope_82]
d_messages_536 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v1 v2 v3 v4 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.history
d_history_538 :: T_State'7501'_520 -> [T_Message_62]
d_history_538 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v1 v2 v3 v4 v5 -> coe v4
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Stateᵍ.adversarialState
d_adversarialState_540 :: T_State'7501'_520 -> AgdaAny
d_adversarialState_540 v0 =
  case coe v0 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v1 v2 v3 v4 v5 -> coe v5
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.Delivered
d_Delivered_544 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  ()
d_Delivered_544 = erased

-- Peras.SmallStep._._._,_,_,_↑_
d__'44'_'44'_'44'_'8593'__554 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Message_62 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  T_LocalState_442 ->
  T_State'7501'_520 ->
  T_State'7501'_520
d__'44'_'44'_'44'_'8593'__554
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
  v15
  v16
  v17
  v18
  v19 =
    du__'44'_'44'_'44'_'8593'__554 v14 v15 v16 v17 v18 v19
du__'44'_'44'_'44'_'8593'__554 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Message_62 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  T_LocalState_442 ->
  T_State'7501'_520 ->
  T_State'7501'_520
du__'44'_'44'_'44'_'8593'__554 v0 v1 v2 v3 v4 v5 =
  case coe v5 of
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v6 v7 v8 v9 v10 ->
      coe
        C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
        (coe v6)
        ( coe
            MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
            MAlonzo.Code.Peras.Block.d_PartyIdO_6
            v3
            v4
            v7
        )
        ( coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__62
            ( coe
                MAlonzo.Code.Data.List.Base.du_map_22
                ( coe
                    MAlonzo.Code.Data.Product.Base.du_uncurry_244
                    ( coe
                        ( \v11 v12 ->
                            coe
                              C_'10629'_'44'_'44'_'44'_'10630'_100
                              (coe v11)
                              (coe v12)
                              (coe v1)
                              (coe v2)
                        )
                    )
                )
                ( coe
                    MAlonzo.Code.Data.List.Base.du_filter_740
                    ( coe
                        ( \v11 ->
                            coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                              ( coe
                                  MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                  (coe v3)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11))
                              )
                        )
                    )
                    (coe v0)
                )
            )
            (coe v8)
        )
        ( coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe v1)
            (coe v9)
        )
        (coe v10)
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.tick
d_tick_580 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520
d_tick_580
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
  v15 =
    du_tick_580 v15
du_tick_580 :: T_State'7501'_520 -> T_State'7501'_520
du_tick_580 v0 =
  coe
    C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
    ( coe
        MAlonzo.Code.Peras.Numbering.d_next_10
        (coe d_clock_532 (coe v0))
    )
    (coe d_stateMap_534 (coe v0))
    ( coe
        MAlonzo.Code.Data.List.Base.du_map_22
        ( coe
            ( \v1 ->
                coe
                  C_'10629'_'44'_'44'_'44'_'10630'_100
                  (coe d_partyId_92 (coe v1))
                  (coe d_honesty_94 (coe v1))
                  (coe d_message_96 (coe v1))
                  ( coe
                      MAlonzo.Code.Data.Fin.Base.du_pred_384
                      (coe d_delay_98 (coe v1))
                  )
            )
        )
        (coe d_messages_536 (coe v0))
    )
    (coe d_history_538 (coe v0))
    (coe d_adversarialState_540 (coe v0))

-- Peras.SmallStep._._._⊢_[_]⇀_
d__'8866'_'91'_'93''8640'__594
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17
  a18
  a19 =
    ()
data T__'8866'_'91'_'93''8640'__594
  = C_honest_616
      T_LocalState_442
      T_LocalState_442
      MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
      T__'91'_'93''8594'__482
  | C_corrupt_636 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34

-- Peras.SmallStep._._._⊢_⇉_
d__'8866'_'8649'__640
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17
  a18 =
    ()
data T__'8866'_'8649'__640
  = C_honest_672
      AgdaAny
      MAlonzo.Code.Peras.Crypto.T_MembershipProof_42
      MAlonzo.Code.Peras.Crypto.T_Signature_70
      MAlonzo.Code.Peras.Chain.T_Vote_4
      AgdaAny
      AgdaAny
      T_VoteInRound_496

-- Peras.SmallStep._._._.adversarialState
d_adversarialState_656 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  AgdaAny
d_adversarialState_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_adversarialState_656 v7
du_adversarialState_656 :: T_State'7501'_520 -> AgdaAny
du_adversarialState_656 v0 = coe d_adversarialState_540 (coe v0)

-- Peras.SmallStep._._._.clock
d_clock_658 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_clock_658 v7
du_clock_658 ::
  T_State'7501'_520 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
du_clock_658 v0 = coe d_clock_532 (coe v0)

-- Peras.SmallStep._._._.history
d_history_660 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  [T_Message_62]
d_history_660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_history_660 v7
du_history_660 :: T_State'7501'_520 -> [T_Message_62]
du_history_660 v0 = coe d_history_538 (coe v0)

-- Peras.SmallStep._._._.messages
d_messages_662 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  [T_Envelope_82]
d_messages_662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_messages_662 v7
du_messages_662 :: T_State'7501'_520 -> [T_Envelope_82]
du_messages_662 v0 = coe d_messages_536 (coe v0)

-- Peras.SmallStep._._._.stateMap
d_stateMap_664 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_stateMap_664 v7
du_stateMap_664 ::
  T_State'7501'_520 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_stateMap_664 v0 = coe d_stateMap_534 (coe v0)

-- Peras.SmallStep._._._⊢_↷_
d__'8866'_'8631'__676
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16
  a17
  a18 =
    ()
data T__'8866'_'8631'__676
  = C_honest_708
      AgdaAny
      MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56
      MAlonzo.Code.Peras.Crypto.T_Signature_70
      MAlonzo.Code.Peras.Block.T_Block_62
      AgdaAny
      AgdaAny
  | C_honest'45'cooldown_752
      AgdaAny
      MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56
      MAlonzo.Code.Peras.Crypto.T_Signature_70
      MAlonzo.Code.Peras.Block.T_Block_62
      AgdaAny
      AgdaAny
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22
      MAlonzo.Code.Data.Nat.Base.T__'8804'__22

-- Peras.SmallStep._._._.adversarialState
d_adversarialState_692 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  AgdaAny
d_adversarialState_692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_adversarialState_692 v7
du_adversarialState_692 :: T_State'7501'_520 -> AgdaAny
du_adversarialState_692 v0 = coe d_adversarialState_540 (coe v0)

-- Peras.SmallStep._._._.clock
d_clock_694 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_clock_694 v7
du_clock_694 ::
  T_State'7501'_520 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
du_clock_694 v0 = coe d_clock_532 (coe v0)

-- Peras.SmallStep._._._.history
d_history_696 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Message_62]
d_history_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_history_696 v7
du_history_696 :: T_State'7501'_520 -> [T_Message_62]
du_history_696 v0 = coe d_history_538 (coe v0)

-- Peras.SmallStep._._._.messages
d_messages_698 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Envelope_82]
d_messages_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_messages_698 v7
du_messages_698 :: T_State'7501'_520 -> [T_Envelope_82]
du_messages_698 v0 = coe d_messages_536 (coe v0)

-- Peras.SmallStep._._._.stateMap
d_stateMap_700 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_stateMap_700 v7
du_stateMap_700 ::
  T_State'7501'_520 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_stateMap_700 v0 = coe d_stateMap_534 (coe v0)

-- Peras.SmallStep._._._.adversarialState
d_adversarialState_724 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  AgdaAny
d_adversarialState_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_adversarialState_724 v7
du_adversarialState_724 :: T_State'7501'_520 -> AgdaAny
du_adversarialState_724 v0 = coe d_adversarialState_540 (coe v0)

-- Peras.SmallStep._._._.clock
d_clock_726 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
d_clock_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_clock_726 v7
du_clock_726 ::
  T_State'7501'_520 -> MAlonzo.Code.Peras.Numbering.T_SlotNumber_4
du_clock_726 v0 = coe d_clock_532 (coe v0)

-- Peras.SmallStep._._._.history
d_history_728 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Message_62]
d_history_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_history_728 v7
du_history_728 :: T_State'7501'_520 -> [T_Message_62]
du_history_728 v0 = coe d_history_538 (coe v0)

-- Peras.SmallStep._._._.messages
d_messages_730 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [T_Envelope_82]
d_messages_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_messages_730 v7
du_messages_730 :: T_State'7501'_520 -> [T_Envelope_82]
du_messages_730 v0 = coe d_messages_536 (coe v0)

-- Peras.SmallStep._._._.stateMap
d_stateMap_732 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  AgdaAny ->
  T_State'7501'_520 ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_stateMap_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 =
  du_stateMap_732 v7
du_stateMap_732 ::
  T_State'7501'_520 -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_stateMap_732 v0 = coe d_stateMap_534 (coe v0)

-- Peras.SmallStep._._._↝_
d__'8605'__762
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T__'8605'__762
  = C_Deliver_766
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T_Message_62
      T__'8866'_'91'_'93''8640'__594
  | C_CastVote_768
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T__'8866'_'8649'__640
  | C_CreateBlock_770
      Integer
      MAlonzo.Code.Peras.Block.T_Honesty_26
      T__'8866'_'8631'__676
  | C_NextSlot_772 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44

-- Peras.SmallStep._._._↝⋆_
d__'8605''8902'__774
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15
  a16 =
    ()
data T__'8605''8902'__774
  = C__'8718'_778
  | C__'8605''10216'_'10217'__786
      T_State'7501'_520
      T__'8605'__762
      T__'8605''8902'__774

-- Peras.SmallStep._._.↝⋆∘↝⋆
d_'8605''8902''8728''8605''8902'_794 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T__'8605''8902'__774 ->
  T__'8605''8902'__774 ->
  T__'8605''8902'__774
d_'8605''8902''8728''8605''8902'_794
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
  v18
  v19 =
    du_'8605''8902''8728''8605''8902'_794 v18 v19
du_'8605''8902''8728''8605''8902'_794 ::
  T__'8605''8902'__774 ->
  T__'8605''8902'__774 ->
  T__'8605''8902'__774
du_'8605''8902''8728''8605''8902'_794 v0 v1 =
  case coe v0 of
    C__'8718'_778 -> coe v1
    C__'8605''10216'_'10217'__786 v3 v5 v6 ->
      coe
        C__'8605''10216'_'10217'__786
        v3
        v5
        (coe du_'8605''8902''8728''8605''8902'_794 (coe v6) (coe v1))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.↝∘↝⋆
d_'8605''8728''8605''8902'_812 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T__'8605''8902'__774 ->
  T__'8605'__762 ->
  T__'8605''8902'__774
d_'8605''8728''8605''8902'_812
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
  v17
  v18
  v19 =
    du_'8605''8728''8605''8902'_812 v17 v18 v19
du_'8605''8728''8605''8902'_812 ::
  T_State'7501'_520 ->
  T__'8605''8902'__774 ->
  T__'8605'__762 ->
  T__'8605''8902'__774
du_'8605''8728''8605''8902'_812 v0 v1 v2 =
  case coe v1 of
    C__'8718'_778 ->
      coe C__'8605''10216'_'10217'__786 v0 v2 (coe C__'8718'_778)
    C__'8605''10216'_'10217'__786 v4 v6 v7 ->
      coe
        C__'8605''10216'_'10217'__786
        v4
        v6
        (coe du_'8605''8728''8605''8902'_812 (coe v0) (coe v7) (coe v2))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.CollisionFree
d_CollisionFree_832
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15 =
    ()
data T_CollisionFree_832
  = C_collision'45'free_846
      MAlonzo.Code.Peras.Block.T_Block_62
      MAlonzo.Code.Peras.Block.T_Block_62
      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44

-- Peras.SmallStep._._._._⊆_
d__'8838'__850 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Message_62] ->
  [T_Message_62] ->
  ()
d__'8838'__850 = erased

-- Peras.SmallStep._._._._⊇_
d__'8839'__852 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Message_62] ->
  [T_Message_62] ->
  ()
d__'8839'__852 = erased

-- Peras.SmallStep._._._._⊆_
d__'8838'__856 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ()
d__'8838'__856 = erased

-- Peras.SmallStep._._.⊆→⊆-cartesianProduct
d_'8838''8594''8838''45'cartesianProduct_868 ::
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_Message_62] ->
  [T_Message_62] ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8838''8594''8838''45'cartesianProduct_868
  ~v0
  ~v1
  ~v2
  ~v3
  ~v4
  v5
  v6
  v7
  v8
  v9 =
    du_'8838''8594''8838''45'cartesianProduct_868 v5 v6 v7 v8 v9
du_'8838''8594''8838''45'cartesianProduct_868 ::
  [T_Message_62] ->
  [T_Message_62] ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8838''8594''8838''45'cartesianProduct_868 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8314'_360
    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
    v1
    v1
    ( coe
        v2
        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
        ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            ( coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                (coe v0)
                (coe v0)
                (coe v3)
                (coe v4)
            )
        )
    )
    ( coe
        v2
        (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
        ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            ( coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                (coe v0)
                (coe v0)
                (coe v3)
                (coe v4)
            )
        )
    )

-- Peras.SmallStep._._.collision-free-resp-⊇
d_collision'45'free'45'resp'45''8839'_884 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T_CollisionFree_832 ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  T_CollisionFree_832
d_collision'45'free'45'resp'45''8839'_884
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
  v17
  v18 =
    du_collision'45'free'45'resp'45''8839'_884 v15 v16 v17 v18
du_collision'45'free'45'resp'45''8839'_884 ::
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T_CollisionFree_832 ->
  ( T_Message_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  T_CollisionFree_832
du_collision'45'free'45'resp'45''8839'_884 v0 v1 v2 v3 =
  case coe v2 of
    C_collision'45'free_846 v4 v5 v6 ->
      coe
        C_collision'45'free_846
        (coe v4)
        (coe v5)
        ( coe
            MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_All'45'resp'45''8839'_214
            ( coe
                MAlonzo.Code.Data.List.Base.du_cartesianProduct_112
                (d_history_538 (coe v1))
                (d_history_538 (coe v1))
            )
            ( coe
                MAlonzo.Code.Data.List.Base.du_cartesianProduct_112
                (d_history_538 (coe v0))
                (d_history_538 (coe v0))
            )
            ( \v7 v8 ->
                coe
                  MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8314'_360
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7))
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
                  (d_history_538 (coe v1))
                  (d_history_538 (coe v1))
                  ( coe
                      v3
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7))
                      ( MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          ( coe
                              MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                              (coe d_history_538 (coe v0))
                              (coe d_history_538 (coe v0))
                              (coe v7)
                              (coe v8)
                          )
                      )
                  )
                  ( coe
                      v3
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
                      ( MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          ( coe
                              MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProduct'8315'_372
                              (coe d_history_538 (coe v0))
                              (coe d_history_538 (coe v0))
                              (coe v7)
                              (coe v8)
                          )
                      )
                  )
            )
            v6
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.[]-hist-common-prefix
d_'91''93''45'hist'45'common'45'prefix_904 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_Message_62 ->
  T__'8866'_'91'_'93''8640'__594 ->
  T_Message_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'91''93''45'hist'45'common'45'prefix_904
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
  v20
  ~v21
  v22 =
    du_'91''93''45'hist'45'common'45'prefix_904 v20 v22
du_'91''93''45'hist'45'common'45'prefix_904 ::
  T__'8866'_'91'_'93''8640'__594 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'91''93''45'hist'45'common'45'prefix_904 v0 v1 =
  coe seq (coe v0) (coe v1)

-- Peras.SmallStep._._.[]⇀-collision-free
d_'91''93''8640''45'collision'45'free_920 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_Message_62 ->
  T_CollisionFree_832 ->
  T__'8866'_'91'_'93''8640'__594 ->
  T_CollisionFree_832
d_'91''93''8640''45'collision'45'free_920
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
  v20
  v21 =
    du_'91''93''8640''45'collision'45'free_920 v20 v21
du_'91''93''8640''45'collision'45'free_920 ::
  T_CollisionFree_832 ->
  T__'8866'_'91'_'93''8640'__594 ->
  T_CollisionFree_832
du_'91''93''8640''45'collision'45'free_920 v0 v1 =
  coe seq (coe v0) (coe seq (coe v1) (coe v0))

-- Peras.SmallStep._._.[]↷-hist-common-prefix
d_'91''93''8631''45'hist'45'common'45'prefix_942 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T__'8866'_'8631'__676 ->
  T_Message_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'91''93''8631''45'hist'45'common'45'prefix_942
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
  v19
  ~v20 =
    du_'91''93''8631''45'hist'45'common'45'prefix_942 v19
du_'91''93''8631''45'hist'45'common'45'prefix_942 ::
  T__'8866'_'8631'__676 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'91''93''8631''45'hist'45'common'45'prefix_942 v0 =
  coe
    seq
    (coe v0)
    ( coe
        MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
    )

-- Peras.SmallStep._._.[]⇉-hist-common-prefix
d_'91''93''8649''45'hist'45'common'45'prefix_960 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T__'8866'_'8649'__640 ->
  T_Message_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'91''93''8649''45'hist'45'common'45'prefix_960
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
  v19
  ~v20 =
    du_'91''93''8649''45'hist'45'common'45'prefix_960 v19
du_'91''93''8649''45'hist'45'common'45'prefix_960 ::
  T__'8866'_'8649'__640 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'91''93''8649''45'hist'45'common'45'prefix_960 v0 =
  coe
    seq
    (coe v0)
    ( coe
        MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
    )

-- Peras.SmallStep._._.[]↷-collision-free
d_'91''93''8631''45'collision'45'free_974 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_CollisionFree_832 ->
  T__'8866'_'8631'__676 ->
  T_CollisionFree_832
d_'91''93''8631''45'collision'45'free_974
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
  ~v17
  ~v18
  v19
  v20 =
    du_'91''93''8631''45'collision'45'free_974 v15 v16 v19 v20
du_'91''93''8631''45'collision'45'free_974 ::
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T_CollisionFree_832 ->
  T__'8866'_'8631'__676 ->
  T_CollisionFree_832
du_'91''93''8631''45'collision'45'free_974 v0 v1 v2 v3 =
  coe
    du_collision'45'free'45'resp'45''8839'_884
    (coe v0)
    (coe v1)
    (coe v2)
    ( \v4 ->
        coe du_'91''93''8631''45'hist'45'common'45'prefix_942 (coe v3)
    )

-- Peras.SmallStep._._.[]⇉-collision-free
d_'91''93''8649''45'collision'45'free_988 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  T_CollisionFree_832 ->
  T__'8866'_'8649'__640 ->
  T_CollisionFree_832
d_'91''93''8649''45'collision'45'free_988
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
  ~v17
  ~v18
  v19
  v20 =
    du_'91''93''8649''45'collision'45'free_988 v15 v16 v19 v20
du_'91''93''8649''45'collision'45'free_988 ::
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T_CollisionFree_832 ->
  T__'8866'_'8649'__640 ->
  T_CollisionFree_832
du_'91''93''8649''45'collision'45'free_988 v0 v1 v2 v3 =
  coe
    du_collision'45'free'45'resp'45''8839'_884
    (coe v0)
    (coe v1)
    (coe v2)
    ( \v4 ->
        coe du_'91''93''8649''45'hist'45'common'45'prefix_960 (coe v3)
    )

-- Peras.SmallStep._._.↝-collision-free
d_'8605''45'collision'45'free_998 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T__'8605'__762 ->
  T_CollisionFree_832 ->
  T_CollisionFree_832
d_'8605''45'collision'45'free_998
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
  v17
  v18 =
    du_'8605''45'collision'45'free_998 v15 v16 v17 v18
du_'8605''45'collision'45'free_998 ::
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T__'8605'__762 ->
  T_CollisionFree_832 ->
  T_CollisionFree_832
du_'8605''45'collision'45'free_998 v0 v1 v2 v3 =
  case coe v2 of
    C_Deliver_766 v4 v5 v8 v9 ->
      coe du_'91''93''8640''45'collision'45'free_920 (coe v3) (coe v9)
    C_CastVote_768 v4 v5 v8 ->
      coe
        du_'91''93''8649''45'collision'45'free_988
        (coe v0)
        (coe v1)
        (coe v3)
        (coe v8)
    C_CreateBlock_770 v4 v5 v8 ->
      coe
        du_'91''93''8631''45'collision'45'free_974
        (coe v0)
        (coe v1)
        (coe v3)
        (coe v8)
    C_NextSlot_772 v5 -> coe v3
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.↝⋆-collision-free
d_'8605''8902''45'collision'45'free_1018 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  ( Integer ->
    MAlonzo.Code.Peras.Numbering.T_RoundNumber_24 ->
    MAlonzo.Code.Peras.Crypto.T_MembershipProof_42 ->
    ()
  ) ->
  ( MAlonzo.Code.Peras.Chain.T_Vote_4 ->
    MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
    ()
  ) ->
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
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  () ->
  T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_State'7501'_520 ->
  T_State'7501'_520 ->
  T__'8605''8902'__774 ->
  T_CollisionFree_832 ->
  T_CollisionFree_832
d_'8605''8902''45'collision'45'free_1018
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
  ~v16
  v17
  v18 =
    du_'8605''8902''45'collision'45'free_1018 v15 v17 v18
du_'8605''8902''45'collision'45'free_1018 ::
  T_State'7501'_520 ->
  T__'8605''8902'__774 ->
  T_CollisionFree_832 ->
  T_CollisionFree_832
du_'8605''8902''45'collision'45'free_1018 v0 v1 v2 =
  case coe v1 of
    C__'8718'_778 -> coe v2
    C__'8605''10216'_'10217'__786 v4 v6 v7 ->
      coe
        du_'8605''45'collision'45'free_998
        (coe v0)
        (coe v4)
        (coe v6)
        ( coe
            du_'8605''8902''45'collision'45'free_1018
            (coe v4)
            (coe v7)
            (coe v2)
        )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep._._.ForgingFree
d_ForgingFree_1030
  a0
  a1
  a2
  a3
  a4
  a5
  a6
  a7
  a8
  a9
  a10
  a11
  a12
  a13
  a14
  a15 =
    ()
data T_ForgingFree_1030
  = C_forging'45'free_1044
      T_State'7501'_520
      MAlonzo.Code.Peras.Block.T_Block_62
      Integer
      T__'8866'_'8631'__676
      MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
