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

module MAlonzo.Code.Peras.SmallStep.Properties where

import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Equality.Propositional
import qualified MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Map
import qualified MAlonzo.Code.Data.Tree.AVL.Map.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Peras.Block
import qualified MAlonzo.Code.Peras.Chain
import qualified MAlonzo.Code.Peras.Crypto
import qualified MAlonzo.Code.Peras.Numbering
import qualified MAlonzo.Code.Peras.Params
import qualified MAlonzo.Code.Peras.SmallStep
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
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

-- Peras.SmallStep.Properties._._⊆_
d__'8838'__12 ::
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ()
d__'8838'__12 = erased

-- Peras.SmallStep.Properties._._⊆_
d__'8838'__16 ::
  [MAlonzo.Code.Peras.SmallStep.T_Envelope_82] ->
  [MAlonzo.Code.Peras.SmallStep.T_Envelope_82] ->
  ()
d__'8838'__16 = erased

-- Peras.SmallStep.Properties.M.Map
d_Map_28 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_28 = erased

-- Peras.SmallStep.Properties.M.empty
d_empty_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_empty_32 v0 v1 = coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_198

-- Peras.SmallStep.Properties.M.insert
d_insert_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insert_42 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)

-- Peras.SmallStep.Properties.M.lookup
d_lookup_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Integer ->
  Maybe AgdaAny
d_lookup_54 v0 v1 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.du_lookup_208
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)

-- Peras.SmallStep.Properties._.∈ₖᵥ-insert⁺
d_'8712''8342''7525''45'insert'8314'_94 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  AgdaAny ->
  ( MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'insert'8314'_94 v0 v1 v2 v3 v4 v5 v6 v7 v8 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.Membership.Propositional.Properties.du_'8712''8342''7525''45'insert'8314'_342
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)
    v1
    v5
    v6
    v8

-- Peras.SmallStep.Properties._.∈ₖᵥ-insert⁺⁺
d_'8712''8342''7525''45'insert'8314''8314'_96 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'insert'8314''8314'_96 v0 v1 v2 v3 v4 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.Membership.Propositional.Properties.du_'8712''8342''7525''45'insert'8314''8314'_362
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)
    v0
    v3
    v4

-- Peras.SmallStep.Properties._.∈ₖᵥ-lookup⁺
d_'8712''8342''7525''45'lookup'8314'_104 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8712''8342''7525''45'lookup'8314'_104 = erased

-- Peras.SmallStep.Properties._.∈ₖᵥ-lookup⁻
d_'8712''8342''7525''45'lookup'8315'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Tree.AVL.Relation.Unary.Any.T_Any_326
d_'8712''8342''7525''45'lookup'8315'_106 v0 v1 v2 v3 v4 v5 =
  coe
    MAlonzo.Code.Data.Tree.AVL.Map.Membership.Propositional.Properties.du_'8712''8342''7525''45'lookup'8315'_468
    (coe MAlonzo.Code.Peras.Block.d_PartyIdO_6)
    v2
    v3
    v4

-- Peras.SmallStep.Properties._._.LocalState′
d_LocalState'8242'_182 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ()
d_LocalState'8242'_182 = erased

-- Peras.SmallStep.Properties._._.GlobalState
d_GlobalState_184 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ()
d_GlobalState_184 = erased

-- Peras.SmallStep.Properties._._.state₀
d_state'8320'_186 ::
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_LocalState_442
d_state'8320'_186 v0 ~v1 ~v2 ~v3 ~v4 = du_state'8320'_186 v0
du_state'8320'_186 ::
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  MAlonzo.Code.Peras.SmallStep.T_LocalState_442
du_state'8320'_186 v0 =
  coe
    MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
    (coe MAlonzo.Code.Peras.SmallStep.d_tree'8320'_406 (coe v0))

-- Peras.SmallStep.Properties._._.states₀
d_states'8320'_188 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_states'8320'_188
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
  v10
  ~v11
  ~v12
  ~v13
  v14 =
    du_states'8320'_188 v10 v14
du_states'8320'_188 ::
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_states'8320'_188 v0 v1 =
  coe
    MAlonzo.Code.Data.List.Base.du_foldr_242
    ( coe
        ( \v2 v3 ->
            case coe v2 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 ->
                coe
                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                  v4
                  ( coe
                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                      (coe MAlonzo.Code.Peras.SmallStep.d_tree'8320'_406 (coe v0))
                  )
                  v3
              _ -> MAlonzo.RTE.mazUnreachableError
        )
    )
    (coe MAlonzo.Code.Data.Tree.AVL.Map.du_empty_198)
    (coe v1)

-- Peras.SmallStep.Properties._._.N₀
d_N'8320'_196 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520
d_N'8320'_196
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
  v10
  ~v11
  v12
  ~v13
  v14 =
    du_N'8320'_196 v10 v12 v14
du_N'8320'_196 ::
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520
du_N'8320'_196 v0 v1 v2 =
  coe
    MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
    ( coe
        MAlonzo.Code.Peras.Numbering.C_MkSlotNumber_16
        (coe (0 :: Integer))
    )
    (coe du_states'8320'_188 (coe v0) (coe v2))
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
    (coe v1)

-- Peras.SmallStep.Properties._._.clock'
d_clock''_198 ::
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer
d_clock''_198 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_clock''_198 v5
du_clock''_198 ::
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 -> Integer
du_clock''_198 v0 =
  coe
    MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
    (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v0))

-- Peras.SmallStep.Properties._._.clock-incr
d_clock'45'incr_204 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605'__764 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_clock'45'incr_204
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
    du_clock'45'incr_204 v15 v16 v17
du_clock'45'incr_204 ::
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605'__764 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_clock'45'incr_204 v0 v1 v2 =
  case coe v0 of
    MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v3 v4 v5 v6 v7 ->
      let v8 =
            seq
              (coe v2)
              ( coe
                  MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2714
                  (coe MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8 (coe v3))
              )
       in coe
            ( case coe v1 of
                MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v9 v10 v11 v12 v13 ->
                  case coe v2 of
                    MAlonzo.Code.Peras.SmallStep.C_Deliver_768 v14 v15 v18 v19 ->
                      coe
                        seq
                        (coe v19)
                        ( coe
                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2646
                            (coe MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8 (coe v3))
                        )
                    MAlonzo.Code.Peras.SmallStep.C_CastVote_770 v14 v15 v18 ->
                      coe
                        seq
                        (coe v18)
                        ( case coe v12 of
                            (:) v19 v20 ->
                              case coe v19 of
                                MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66 v21 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2646
                                    ( coe
                                        MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                        (coe v3)
                                    )
                                _ -> coe v8
                            _ -> coe v8
                        )
                    MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772 v14 v15 v18 ->
                      coe
                        seq
                        (coe v18)
                        ( case coe v12 of
                            (:) v19 v20 ->
                              case coe v19 of
                                MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64 v21 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2646
                                    ( coe
                                        MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                        (coe v3)
                                    )
                                _ -> coe v8
                            _ -> coe v8
                        )
                    MAlonzo.Code.Peras.SmallStep.C_NextSlot_774 v15 ->
                      coe
                        MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2714
                        (coe MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
            )
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._.clock-incr⋆
d_clock'45'incr'8902'_222 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_clock'45'incr'8902'_222
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
  v17 =
    du_clock'45'incr'8902'_222 v15 v17
du_clock'45'incr'8902'_222 ::
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_clock'45'incr'8902'_222 v0 v1 =
  case coe v1 of
    MAlonzo.Code.Peras.SmallStep.C_'91''93''8242'_778 ->
      coe
        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2646
        ( coe
            MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
            (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v0))
        )
    MAlonzo.Code.Peras.SmallStep.C__'8759''8242'__780 v3 v5 v6 ->
      coe
        MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2654
        (coe du_clock'45'incr_204 (coe v0) (coe v3) (coe v5))
        (coe du_clock'45'incr'8902'_222 (coe v3) (coe v6))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._.All-∷=
d_All'45''8759''61'_244 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45''8759''61'_244
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
  v21
  v22
  v23
  v24 =
    du_All'45''8759''61'_244 v21 v22 v23 v24
du_All'45''8759''61'_244 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45''8759''61'_244 v0 v1 v2 v3 =
  case coe v1 of
    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7 ->
      case coe v0 of
        (:) v8 v9 ->
          case coe v2 of
            MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v12 ->
              coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                v3
                v7
            MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v12 ->
              coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                v6
                (coe du_All'45''8759''61'_244 (coe v9) (coe v7) (coe v12) (coe v3))
            _ -> MAlonzo.RTE.mazUnreachableError
        _ -> MAlonzo.RTE.mazUnreachableError
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._.knowledge-propagation₁
d_knowledge'45'propagation'8321'_288 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.knowledge-propagation\8321"

-- Peras.SmallStep.Properties._._.x∈x∷xs
d_x'8712'x'8759'xs_294 ::
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_x'8712'x'8759'xs_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 =
  du_x'8712'x'8759'xs_294
du_x'8712'x'8759'xs_294 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_x'8712'x'8759'xs_294 =
  coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased

-- Peras.SmallStep.Properties._._.blocksNotLost
d_blocksNotLost_312 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.blocksNotLost"

-- Peras.SmallStep.Properties._._.e∈m′∈ms∷=m′
d_e'8712'm'8242''8712'ms'8759''61'm'8242'_324 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.e\8712m\8242\8712ms\8759=m\8242"

-- Peras.SmallStep.Properties._._.m′∈ms─m∈ms
d_m'8242''8712'ms'9472'm'8712'ms_334 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.m\8242\8712ms\9472m\8712ms"

-- Peras.SmallStep.Properties._._.VoteMsg≢BlockMsg
d_VoteMsg'8802'BlockMsg_344 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Peras.Chain.T_Vote_4 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_VoteMsg'8802'BlockMsg_344 = erased

-- Peras.SmallStep.Properties._._.⊆-vote
d_'8838''45'vote_362 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.SmallStep.T__'8866'_'8649'__640 ->
  MAlonzo.Code.Peras.SmallStep.T_Envelope_82 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8838''45'vote_362
  v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  v6
  ~v7
  v8
  ~v9
  v10
  ~v11
  ~v12
  ~v13
  v14
  v15
  ~v16
  v17
  ~v18
  v19
  ~v20 =
    du_'8838''45'vote_362 v0 v6 v8 v10 v14 v15 v17 v19
du_'8838''45'vote_362 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.SmallStep.T__'8866'_'8649'__640 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8838''45'vote_362 v0 v1 v2 v3 v4 v5 v6 v7 =
  case coe v7 of
    MAlonzo.Code.Peras.SmallStep.C_honest_672 v9 v11 v12 v13 v16 v18 v19 ->
      coe
        MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_208
        ( coe
            MAlonzo.Code.Data.List.Base.du_map_22
            ( coe
                MAlonzo.Code.Data.Product.Base.du_uncurry_244
                ( coe
                    ( \v20 v21 ->
                        coe
                          MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                          (coe v20)
                          (coe v21)
                          ( coe
                              MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                              ( coe
                                  MAlonzo.Code.Peras.Chain.C_MkVote_26
                                  ( coe
                                      MAlonzo.Code.Peras.Numbering.C_MkRoundNumber_32
                                      ( coe
                                          MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                          ( coe
                                              MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                              (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v5))
                                          )
                                          (coe MAlonzo.Code.Peras.Params.d_T_24 (coe v2))
                                      )
                                  )
                                  (coe v6)
                                  (coe v11)
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                      v1
                                      ( coe
                                          MAlonzo.Code.Peras.Chain.du_tip_172
                                          (coe v0)
                                          (coe v1)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                              v3
                                              ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                  (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v5))
                                                  (coe MAlonzo.Code.Peras.Params.d_L_30 (coe v2))
                                              )
                                              v9
                                          )
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_valid_328
                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                  (coe v3)
                                              )
                                              v9
                                              ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                  (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v5))
                                                  (coe MAlonzo.Code.Peras.Params.d_L_30 (coe v2))
                                              )
                                          )
                                      )
                                  )
                                  (coe v12)
                              )
                          )
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                    )
                )
            )
            ( coe
                MAlonzo.Code.Data.List.Base.du_filter_740
                ( coe
                    ( \v20 ->
                        coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                          ( coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                              (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v20))
                          )
                    )
                )
                (coe v4)
            )
        )
        (MAlonzo.Code.Peras.SmallStep.d_messages_536 (coe v5))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._.⊆-block
d_'8838''45'block_382 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.SmallStep.T__'8866'_'8631'__676 ->
  MAlonzo.Code.Peras.SmallStep.T_Envelope_82 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8838''45'block_382
  v0
  ~v1
  ~v2
  ~v3
  ~v4
  ~v5
  v6
  v7
  ~v8
  ~v9
  v10
  ~v11
  ~v12
  v13
  v14
  v15
  ~v16
  v17
  ~v18
  v19
  ~v20 =
    du_'8838''45'block_382 v0 v6 v7 v10 v13 v14 v15 v17 v19
du_'8838''45'block_382 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  MAlonzo.Code.Peras.SmallStep.T__'8866'_'8631'__676 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8838''45'block_382 v0 v1 v2 v3 v4 v5 v6 v7 v8 =
  case coe v8 of
    MAlonzo.Code.Peras.SmallStep.C_honest_708 v10 v12 v13 v14 v17 v18 ->
      coe
        MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_208
        ( coe
            MAlonzo.Code.Data.List.Base.du_map_22
            ( coe
                MAlonzo.Code.Data.Product.Base.du_uncurry_244
                ( coe
                    ( \v19 v20 ->
                        coe
                          MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                          (coe v19)
                          (coe v20)
                          ( coe
                              MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                              ( coe
                                  MAlonzo.Code.Peras.Block.C_MkBlock_110
                                  (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                  (coe v7)
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                      v1
                                      ( coe
                                          MAlonzo.Code.Peras.Chain.du_tip_172
                                          (coe v0)
                                          (coe v1)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                              v3
                                              (MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                              v10
                                          )
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_valid_328
                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                  (coe v3)
                                              )
                                              v10
                                              (MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                          )
                                      )
                                  )
                                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                  (coe v12)
                                  (coe v13)
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                      v2
                                      ( coe
                                          v4
                                          (MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                          v7
                                      )
                                  )
                              )
                          )
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                    )
                )
            )
            ( coe
                MAlonzo.Code.Data.List.Base.du_filter_740
                ( coe
                    ( \v19 ->
                        coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                          ( coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                              (coe v7)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v19))
                          )
                    )
                )
                (coe v5)
            )
        )
        (MAlonzo.Code.Peras.SmallStep.d_messages_536 (coe v6))
    MAlonzo.Code.Peras.SmallStep.C_honest'45'cooldown_752 v10 v12 v13 v14 v17 v18 v20 v21 ->
      coe
        MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_208
        ( coe
            MAlonzo.Code.Data.List.Base.du_map_22
            ( coe
                MAlonzo.Code.Data.Product.Base.du_uncurry_244
                ( coe
                    ( \v22 v23 ->
                        coe
                          MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                          (coe v22)
                          (coe v23)
                          ( coe
                              MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                              ( coe
                                  MAlonzo.Code.Peras.Block.C_MkBlock_110
                                  (coe MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                  (coe v7)
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                      v1
                                      ( coe
                                          MAlonzo.Code.Peras.Chain.du_tip_172
                                          (coe v0)
                                          (coe v1)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                              v3
                                              (MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                              v10
                                          )
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_valid_328
                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                  (coe v3)
                                              )
                                              v10
                                              (MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                          )
                                      )
                                  )
                                  (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                  (coe v12)
                                  (coe v13)
                                  ( coe
                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                      v2
                                      ( coe
                                          v4
                                          (MAlonzo.Code.Peras.SmallStep.d_clock_532 (coe v6))
                                          v7
                                      )
                                  )
                              )
                          )
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                    )
                )
            )
            ( coe
                MAlonzo.Code.Data.List.Base.du_filter_740
                ( coe
                    ( \v22 ->
                        coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                          ( coe
                              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                              (coe v7)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v22))
                          )
                    )
                )
                (coe v5)
            )
        )
        (MAlonzo.Code.Peras.SmallStep.d_messages_536 (coe v6))
    _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._.knowledge-propagation₂
d_knowledge'45'propagation'8322'_416 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_knowledge'45'propagation'8322'_416
  v0
  v1
  ~v2
  ~v3
  ~v4
  ~v5
  v6
  v7
  v8
  ~v9
  v10
  ~v11
  v12
  v13
  v14
  v15
  v16
  v17
  v18
  ~v19
  v20
  ~v21
  ~v22
  v23
  ~v24
  ~v25
  ~v26 =
    du_knowledge'45'propagation'8322'_416
      v0
      v1
      v6
      v7
      v8
      v10
      v12
      v13
      v14
      v15
      v16
      v17
      v18
      v20
      v23
du_knowledge'45'propagation'8322'_416 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_knowledge'45'propagation'8322'_416
  v0
  v1
  v2
  v3
  v4
  v5
  v6
  v7
  v8
  v9
  v10
  v11
  v12
  v13
  v14 =
    case coe v14 of
      MAlonzo.Code.Peras.SmallStep.C_'91''93''8242'_778 ->
        coe
          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_38
      MAlonzo.Code.Peras.SmallStep.C__'8759''8242'__780 v16 v18 v19 ->
        case coe v18 of
          MAlonzo.Code.Peras.SmallStep.C_Deliver_768 v20 v21 v24 v25 ->
            case coe v25 of
              MAlonzo.Code.Peras.SmallStep.C_honest_616 v27 v28 v36 v37 ->
                case coe v9 of
                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v38 v39 v40 v41 v42 ->
                    case coe v37 of
                      MAlonzo.Code.Peras.SmallStep.C_VoteReceived_488 ->
                        case coe v24 of
                          MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66 v45 ->
                            case coe v27 of
                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452 v46 ->
                                coe
                                  du_knowledge'45'propagation'8322'_416
                                  (coe v0)
                                  (coe v1)
                                  (coe v2)
                                  (coe v3)
                                  (coe v4)
                                  (coe v5)
                                  (coe v6)
                                  (coe v7)
                                  (coe v8)
                                  ( coe
                                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                      (coe v38)
                                      ( coe
                                          MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                          MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                          v20
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                  v5
                                                  v46
                                                  v45
                                              )
                                          )
                                          v39
                                      )
                                      ( coe
                                          MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                          (coe v40)
                                          (coe v36)
                                      )
                                      (coe v41)
                                      (coe v42)
                                  )
                                  (coe v10)
                                  (coe v11)
                                  (coe v12)
                                  (coe v13)
                                  (coe v19)
                              _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Peras.SmallStep.C_BlockReceived_494 ->
                        case coe v24 of
                          MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64 v45 ->
                            case coe v27 of
                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452 v46 ->
                                let v47 =
                                      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                        (coe v11)
                                        (coe v20)
                                 in coe
                                      ( case coe v47 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v48 v49 ->
                                            if coe v48
                                              then
                                                coe
                                                  seq
                                                  (coe v49)
                                                  ( let v50 =
                                                          coe
                                                            MAlonzo.Code.Peras.Block.d__'8799''45'Block__112
                                                            v45
                                                            v13
                                                     in coe
                                                          ( case coe v50 of
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v51 v52 ->
                                                                if coe v51
                                                                  then
                                                                    coe
                                                                      seq
                                                                      ( coe
                                                                          v52
                                                                      )
                                                                      ( coe
                                                                          d_blocksNotLost_312
                                                                          v0
                                                                          v1
                                                                          erased
                                                                          erased
                                                                          erased
                                                                          erased
                                                                          v2
                                                                          v3
                                                                          v4
                                                                          erased
                                                                          v5
                                                                          erased
                                                                          v6
                                                                          v7
                                                                          v8
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                                              ( coe
                                                                                  v38
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Data.Tree.AVL.du_insert_286
                                                                                  ( coe
                                                                                      MAlonzo.Code.Data.Nat.Properties.d_'60''45'strictTotalOrder_2922
                                                                                  )
                                                                                  ( coe
                                                                                      MAlonzo.Code.Data.Tree.AVL.Value.C_MkValue_50
                                                                                      ( \v53
                                                                                         v54
                                                                                         v55
                                                                                         v56 ->
                                                                                            v56
                                                                                      )
                                                                                  )
                                                                                  ( coe
                                                                                      v20
                                                                                  )
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                                      ( coe
                                                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                          v5
                                                                                          v46
                                                                                          v45
                                                                                      )
                                                                                  )
                                                                                  ( coe
                                                                                      v39
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Data.List.Base.du_removeAt_662
                                                                                  ( coe
                                                                                      v40
                                                                                  )
                                                                                  ( coe
                                                                                      MAlonzo.Code.Data.List.Relation.Unary.Any.du_index_86
                                                                                      ( coe
                                                                                          v40
                                                                                      )
                                                                                      ( coe
                                                                                          v36
                                                                                      )
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  v41
                                                                              )
                                                                              ( coe
                                                                                  v42
                                                                              )
                                                                          )
                                                                          v10
                                                                          v11
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                              v5
                                                                              v46
                                                                              v45
                                                                          )
                                                                          v12
                                                                          v13
                                                                          v19
                                                                          erased
                                                                          erased
                                                                          ( coe
                                                                              MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'resp'45''8779'_76
                                                                              v13
                                                                              ( coe
                                                                                  MAlonzo.Code.Peras.SmallStep.d_allBlocks_410
                                                                                  v5
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                      v5
                                                                                      v46
                                                                                      v13
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Peras.SmallStep.d_allBlocks_410
                                                                                  v5
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                      v5
                                                                                      v46
                                                                                      v45
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Data.List.Relation.Binary.Equality.Propositional.du_'8801''8658''8779'_78
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.SmallStep.d_allBlocks_410
                                                                                      v5
                                                                                      ( coe
                                                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                          v5
                                                                                          v46
                                                                                          v13
                                                                                      )
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.SmallStep.d_extendable_316
                                                                                      ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                                          ( coe
                                                                                              v5
                                                                                          )
                                                                                      )
                                                                                      v46
                                                                                      v13
                                                                                  )
                                                                                  v13
                                                                                  ( coe
                                                                                      MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                                      erased
                                                                                  )
                                                                              )
                                                                          )
                                                                      )
                                                                  else
                                                                    coe
                                                                      seq
                                                                      ( coe
                                                                          v52
                                                                      )
                                                                      ( coe
                                                                          du_knowledge'45'propagation'8322'_416
                                                                          ( coe
                                                                              v0
                                                                          )
                                                                          ( coe
                                                                              v1
                                                                          )
                                                                          ( coe
                                                                              v2
                                                                          )
                                                                          ( coe
                                                                              v3
                                                                          )
                                                                          ( coe
                                                                              v4
                                                                          )
                                                                          ( coe
                                                                              v5
                                                                          )
                                                                          ( coe
                                                                              v6
                                                                          )
                                                                          ( coe
                                                                              v7
                                                                          )
                                                                          ( coe
                                                                              v8
                                                                          )
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                                              ( coe
                                                                                  v38
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                                  v20
                                                                                  ( coe
                                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                                      ( coe
                                                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                          v5
                                                                                          v46
                                                                                          v45
                                                                                      )
                                                                                  )
                                                                                  v39
                                                                              )
                                                                              ( coe
                                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                                  ( coe
                                                                                      v40
                                                                                  )
                                                                                  ( coe
                                                                                      v36
                                                                                  )
                                                                              )
                                                                              ( coe
                                                                                  v41
                                                                              )
                                                                              ( coe
                                                                                  v42
                                                                              )
                                                                          )
                                                                          ( coe
                                                                              v10
                                                                          )
                                                                          ( coe
                                                                              v11
                                                                          )
                                                                          ( coe
                                                                              v12
                                                                          )
                                                                          ( coe
                                                                              v13
                                                                          )
                                                                          ( coe
                                                                              v19
                                                                          )
                                                                      )
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                          )
                                                  )
                                              else
                                                coe
                                                  seq
                                                  (coe v49)
                                                  ( coe
                                                      du_knowledge'45'propagation'8322'_416
                                                      (coe v0)
                                                      (coe v1)
                                                      (coe v2)
                                                      (coe v3)
                                                      (coe v4)
                                                      (coe v5)
                                                      (coe v6)
                                                      (coe v7)
                                                      (coe v8)
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                          (coe v38)
                                                          ( coe
                                                              MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                              MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                              v20
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                      v5
                                                                      v46
                                                                      v45
                                                                  )
                                                              )
                                                              v39
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                              (coe v40)
                                                              (coe v36)
                                                          )
                                                          (coe v41)
                                                          (coe v42)
                                                      )
                                                      (coe v10)
                                                      (coe v11)
                                                      (coe v12)
                                                      (coe v13)
                                                      (coe v19)
                                                  )
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                      )
                              _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Peras.SmallStep.C_corrupt_636 v34 ->
                case coe v9 of
                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v35 v36 v37 v38 v39 ->
                    case coe v16 of
                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v40 v41 v42 v43 v44 ->
                        coe
                          du_knowledge'45'propagation'8322'_416
                          (coe v0)
                          (coe v1)
                          (coe v2)
                          (coe v3)
                          (coe v4)
                          (coe v5)
                          (coe v6)
                          (coe v7)
                          (coe v8)
                          ( coe
                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                              (coe v35)
                              (coe v36)
                              ( coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du__'8759''61'__102
                                  (coe v37)
                                  (coe v34)
                                  ( coe
                                      MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                      (coe v20)
                                      (coe MAlonzo.Code.Peras.Block.C_Corrupt_34)
                                      (coe v24)
                                      ( coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                      )
                                  )
                              )
                              (coe v38)
                              (coe v44)
                          )
                          (coe v10)
                          (coe v11)
                          (coe v12)
                          (coe v13)
                          (coe v19)
                      _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
          MAlonzo.Code.Peras.SmallStep.C_CastVote_770 v20 v21 v24 ->
            coe
              du_knowledge'45'propagation'8322'_416
              (coe v0)
              (coe v1)
              (coe v2)
              (coe v3)
              (coe v4)
              (coe v5)
              (coe v6)
              (coe v7)
              (coe v8)
              (coe v16)
              (coe v10)
              (coe v11)
              (coe v12)
              (coe v13)
              (coe v19)
          MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772 v20 v21 v24 ->
            coe
              du_knowledge'45'propagation'8322'_416
              (coe v0)
              (coe v1)
              (coe v2)
              (coe v3)
              (coe v4)
              (coe v5)
              (coe v6)
              (coe v7)
              (coe v8)
              (coe v16)
              (coe v10)
              (coe v11)
              (coe v12)
              (coe v13)
              (coe v19)
          MAlonzo.Code.Peras.SmallStep.C_NextSlot_774 v21 ->
            coe
              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_38
          _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._.knowledge-propagation₀
d_knowledge'45'propagation'8320'_780 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_knowledge'45'propagation'8320'_780
  v0
  v1
  ~v2
  ~v3
  ~v4
  ~v5
  v6
  v7
  v8
  ~v9
  v10
  ~v11
  v12
  v13
  v14
  v15
  v16
  v17
  v18
  v19
  v20
  ~v21
  v22
  ~v23
  v24
  ~v25
  ~v26
  v27
  v28
  v29 =
    du_knowledge'45'propagation'8320'_780
      v0
      v1
      v6
      v7
      v8
      v10
      v12
      v13
      v14
      v15
      v16
      v17
      v18
      v19
      v20
      v22
      v24
      v27
      v28
      v29
du_knowledge'45'propagation'8320'_780 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_knowledge'45'propagation'8320'_780
  v0
  v1
  v2
  v3
  v4
  v5
  v6
  v7
  v8
  v9
  v10
  v11
  v12
  v13
  v14
  v15
  v16
  v17
  v18
  v19 =
    let v20 =
          coe
            d_knowledge'45'propagation'8321'_288
            v0
            v1
            erased
            erased
            erased
            erased
            v2
            v3
            v4
            erased
            v5
            erased
            v6
            v7
            v8
            v9
            v10
            v11
            v12
            v13
            v14
            v18
            v15
            v16
            v17
            erased
            v19
     in coe
          ( case coe v20 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22 ->
                case coe v21 of
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24 ->
                    case coe v22 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26 ->
                        case coe v25 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28 ->
                            case coe v28 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30 ->
                                case coe v26 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32 ->
                                    case coe v32 of
                                      MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v35 ->
                                        case coe v24 of
                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v36 v37 v38 v39 v40 ->
                                            case coe v38 of
                                              (:) v41 v42 ->
                                                coe
                                                  du_knowledge'45'propagation'8322'_416
                                                  (coe v0)
                                                  (coe v1)
                                                  (coe v2)
                                                  (coe v3)
                                                  (coe v4)
                                                  (coe v5)
                                                  (coe v6)
                                                  (coe v7)
                                                  (coe v8)
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                      (coe v36)
                                                      (coe v37)
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                              (coe v11)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_Honest_30
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                  (coe v18)
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                              )
                                                          )
                                                          (coe v42)
                                                      )
                                                      (coe v39)
                                                      (coe v40)
                                                  )
                                                  (coe v9)
                                                  (coe v11)
                                                  (coe v13)
                                                  (coe v18)
                                                  (coe v30)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v35 ->
                                        coe
                                          du_knowledge'45'propagation'8322'_416
                                          (coe v0)
                                          (coe v1)
                                          (coe v2)
                                          (coe v3)
                                          (coe v4)
                                          (coe v5)
                                          (coe v6)
                                          (coe v7)
                                          (coe v8)
                                          (coe v24)
                                          (coe v9)
                                          (coe v11)
                                          (coe v13)
                                          (coe v18)
                                          (coe v30)
                                      _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
          )

-- Peras.SmallStep.Properties._._.knowledge-propagation
d_knowledge'45'propagation_896 ::
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_knowledge'45'propagation_896
  v0
  v1
  ~v2
  ~v3
  ~v4
  ~v5
  v6
  v7
  v8
  ~v9
  v10
  ~v11
  v12
  v13
  v14
  v15
  ~v16
  v17
  v18
  v19
  v20
  v21
  ~v22
  ~v23
  ~v24
  v25
  ~v26
  v27
  v28
  ~v29
  ~v30
  v31
  ~v32
  v33 =
    du_knowledge'45'propagation_896
      v0
      v1
      v6
      v7
      v8
      v10
      v12
      v13
      v14
      v15
      v17
      v18
      v19
      v20
      v21
      v25
      v27
      v28
      v31
      v33
du_knowledge'45'propagation_896 ::
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Certificate_66 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Crypto.T_Hashable_34 ->
  MAlonzo.Code.Peras.Params.T_Params_4 ->
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_knowledge'45'propagation_896
  v0
  v1
  v2
  v3
  v4
  v5
  v6
  v7
  v8
  v9
  v10
  v11
  v12
  v13
  v14
  v15
  v16
  v17
  v18
  v19 =
    case coe v17 of
      MAlonzo.Code.Peras.SmallStep.C_'91''93''8242'_778 ->
        coe
          du_knowledge'45'propagation'8320'_780
          (coe v0)
          (coe v1)
          (coe v2)
          (coe v3)
          (coe v4)
          (coe v5)
          (coe v6)
          (coe v7)
          (coe v8)
          (coe v9)
          (coe v10)
          (coe v11)
          (coe v12)
          (coe v13)
          (coe v14)
          (coe v15)
          (coe v16)
          (coe v18)
          (coe v19)
      MAlonzo.Code.Peras.SmallStep.C__'8759''8242'__780 v21 v23 v24 ->
        case coe v23 of
          MAlonzo.Code.Peras.SmallStep.C_Deliver_768 v25 v26 v29 v30 ->
            case coe v30 of
              MAlonzo.Code.Peras.SmallStep.C_honest_616 v32 v33 v41 v42 ->
                case coe v9 of
                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v43 v44 v45 v46 v47 ->
                    case coe v42 of
                      MAlonzo.Code.Peras.SmallStep.C_VoteReceived_488 ->
                        case coe v29 of
                          MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66 v50 ->
                            case coe v32 of
                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452 v51 ->
                                let v52 =
                                      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                        (coe v10)
                                        (coe v25)
                                 in coe
                                      ( case coe v52 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v53 v54 ->
                                            if coe v53
                                              then
                                                coe
                                                  seq
                                                  (coe v54)
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_extendable'45'votes_322
                                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                  (coe v5)
                                                              )
                                                              v12
                                                              v50
                                                          )
                                                      )
                                                      ( coe
                                                          du_knowledge'45'propagation_896
                                                          (coe v0)
                                                          (coe v1)
                                                          (coe v2)
                                                          (coe v3)
                                                          (coe v4)
                                                          (coe v5)
                                                          (coe v6)
                                                          (coe v7)
                                                          (coe v8)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                              (coe v43)
                                                              ( coe
                                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                  v25
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                                          v5
                                                                          v51
                                                                          v50
                                                                      )
                                                                  )
                                                                  v44
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                  (coe v45)
                                                                  (coe v41)
                                                              )
                                                              (coe v46)
                                                              (coe v47)
                                                          )
                                                          (coe v10)
                                                          (coe v11)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                              v5
                                                              v12
                                                              v50
                                                          )
                                                          (coe v13)
                                                          (coe v14)
                                                          (coe v15)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                                  (coe v43)
                                                                  ( coe
                                                                      MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                      MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                      v25
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                                              v5
                                                                              v51
                                                                              v50
                                                                          )
                                                                      )
                                                                      v44
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                      (coe v45)
                                                                      (coe v41)
                                                                  )
                                                                  (coe v46)
                                                                  (coe v47)
                                                              )
                                                              (coe v16)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_Deliver_768
                                                                  v25
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Block.C_Honest_30
                                                                  )
                                                                  v29
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_honest_616
                                                                      v32
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                                              v5
                                                                              v51
                                                                              v50
                                                                          )
                                                                      )
                                                                      v41
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.C_VoteReceived_488
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                          (coe v24)
                                                          (coe v18)
                                                      )
                                                      (coe v19)
                                                  )
                                              else
                                                coe
                                                  seq
                                                  (coe v54)
                                                  ( coe
                                                      du_knowledge'45'propagation_896
                                                      (coe v0)
                                                      (coe v1)
                                                      (coe v2)
                                                      (coe v3)
                                                      (coe v4)
                                                      (coe v5)
                                                      (coe v6)
                                                      (coe v7)
                                                      (coe v8)
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                          (coe v43)
                                                          ( coe
                                                              MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                              MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                              v25
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                                      v5
                                                                      v51
                                                                      v50
                                                                  )
                                                              )
                                                              v44
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                              (coe v45)
                                                              (coe v41)
                                                          )
                                                          (coe v46)
                                                          (coe v47)
                                                      )
                                                      (coe v10)
                                                      (coe v11)
                                                      (coe v12)
                                                      (coe v13)
                                                      (coe v14)
                                                      (coe v15)
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                              (coe v43)
                                                              ( coe
                                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                  v25
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                                          v5
                                                                          v51
                                                                          v50
                                                                      )
                                                                  )
                                                                  v44
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                  (coe v45)
                                                                  (coe v41)
                                                              )
                                                              (coe v46)
                                                              (coe v47)
                                                          )
                                                          (coe v16)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_Deliver_768
                                                              v25
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_Honest_30
                                                              )
                                                              v29
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_honest_616
                                                                  v32
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                                          v5
                                                                          v51
                                                                          v50
                                                                      )
                                                                  )
                                                                  v41
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_VoteReceived_488
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      (coe v24)
                                                      (coe v18)
                                                      (coe v19)
                                                  )
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                      )
                              _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Peras.SmallStep.C_BlockReceived_494 ->
                        case coe v29 of
                          MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64 v50 ->
                            case coe v32 of
                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452 v51 ->
                                let v52 =
                                      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                        (coe v10)
                                        (coe v25)
                                 in coe
                                      ( case coe v52 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v53 v54 ->
                                            if coe v53
                                              then
                                                coe
                                                  seq
                                                  (coe v54)
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
                                                      ( \v55 ->
                                                          coe
                                                            MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
                                                          ( coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_extendable_316
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v12
                                                                  v50
                                                              )
                                                          )
                                                          ( coe
                                                              du_knowledge'45'propagation_896
                                                              (coe v0)
                                                              (coe v1)
                                                              (coe v2)
                                                              (coe v3)
                                                              (coe v4)
                                                              (coe v5)
                                                              (coe v6)
                                                              (coe v7)
                                                              (coe v8)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                                  (coe v43)
                                                                  ( coe
                                                                      MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                      MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                      v25
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                              v5
                                                                              v51
                                                                              v50
                                                                          )
                                                                      )
                                                                      v44
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                      (coe v45)
                                                                      (coe v41)
                                                                  )
                                                                  (coe v46)
                                                                  (coe v47)
                                                              )
                                                              (coe v10)
                                                              (coe v11)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                  v5
                                                                  v12
                                                                  v50
                                                              )
                                                              (coe v13)
                                                              (coe v14)
                                                              (coe v15)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                                      (coe v43)
                                                                      ( coe
                                                                          MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                          MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                          v25
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                              ( coe
                                                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                  v5
                                                                                  v51
                                                                                  v50
                                                                              )
                                                                          )
                                                                          v44
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                          (coe v45)
                                                                          (coe v41)
                                                                      )
                                                                      (coe v46)
                                                                      (coe v47)
                                                                  )
                                                                  (coe v16)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_Deliver_768
                                                                      v25
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.Block.C_Honest_30
                                                                      )
                                                                      v29
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.C_honest_616
                                                                          v32
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                              ( coe
                                                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                                  v5
                                                                                  v51
                                                                                  v50
                                                                              )
                                                                          )
                                                                          v41
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.C_BlockReceived_494
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                              (coe v24)
                                                              (coe v18)
                                                          )
                                                      )
                                                      (coe v19)
                                                  )
                                              else
                                                coe
                                                  seq
                                                  (coe v54)
                                                  ( coe
                                                      du_knowledge'45'propagation_896
                                                      (coe v0)
                                                      (coe v1)
                                                      (coe v2)
                                                      (coe v3)
                                                      (coe v4)
                                                      (coe v5)
                                                      (coe v6)
                                                      (coe v7)
                                                      (coe v8)
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                          (coe v43)
                                                          ( coe
                                                              MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                              MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                              v25
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                      v5
                                                                      v51
                                                                      v50
                                                                  )
                                                              )
                                                              v44
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                              (coe v45)
                                                              (coe v41)
                                                          )
                                                          (coe v46)
                                                          (coe v47)
                                                      )
                                                      (coe v10)
                                                      (coe v11)
                                                      (coe v12)
                                                      (coe v13)
                                                      (coe v14)
                                                      (coe v15)
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                              (coe v43)
                                                              ( coe
                                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                                  v25
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                          v5
                                                                          v51
                                                                          v50
                                                                      )
                                                                  )
                                                                  v44
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du__'9472'__114
                                                                  (coe v45)
                                                                  (coe v41)
                                                              )
                                                              (coe v46)
                                                              (coe v47)
                                                          )
                                                          (coe v16)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_Deliver_768
                                                              v25
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_Honest_30
                                                              )
                                                              v29
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.C_honest_616
                                                                  v32
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                          v5
                                                                          v51
                                                                          v50
                                                                      )
                                                                  )
                                                                  v41
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.C_BlockReceived_494
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      (coe v24)
                                                      (coe v18)
                                                      (coe v19)
                                                  )
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                      )
                              _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Peras.SmallStep.C_corrupt_636 v39 ->
                case coe v9 of
                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v40 v41 v42 v43 v44 ->
                    case coe v21 of
                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542 v45 v46 v47 v48 v49 ->
                        let v50 =
                              MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                (coe v10)
                                (coe v25)
                         in coe
                              ( case coe v50 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v51 v52 ->
                                    if coe v51
                                      then
                                        coe
                                          seq
                                          (coe v52)
                                          ( coe
                                              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_38
                                          )
                                      else
                                        coe
                                          seq
                                          (coe v52)
                                          ( coe
                                              du_knowledge'45'propagation_896
                                              (coe v0)
                                              (coe v1)
                                              (coe v2)
                                              (coe v3)
                                              (coe v4)
                                              (coe v5)
                                              (coe v6)
                                              (coe v7)
                                              (coe v8)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                  (coe v40)
                                                  (coe v41)
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.Any.du__'8759''61'__102
                                                      (coe v42)
                                                      (coe v39)
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                          (coe v25)
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_Corrupt_34
                                                          )
                                                          (coe v29)
                                                          ( coe
                                                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                              ( coe
                                                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                              )
                                                          )
                                                      )
                                                  )
                                                  (coe v43)
                                                  (coe v49)
                                              )
                                              (coe v10)
                                              (coe v11)
                                              (coe v12)
                                              (coe v13)
                                              (coe v14)
                                              (coe v15)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                      (coe v40)
                                                      (coe v41)
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.du__'8759''61'__102
                                                          (coe v42)
                                                          (coe v39)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                              (coe v25)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_Corrupt_34
                                                              )
                                                              (coe v29)
                                                              ( coe
                                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                  ( coe
                                                                      MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      (coe v43)
                                                      (coe v49)
                                                  )
                                                  (coe v16)
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_Deliver_768
                                                      v25
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_Corrupt_34
                                                      )
                                                      v29
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_corrupt_636
                                                          v39
                                                      )
                                                  )
                                              )
                                              (coe v24)
                                              (coe v18)
                                              (coe v19)
                                          )
                                  _ -> MAlonzo.RTE.mazUnreachableError
                              )
                      _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError
          MAlonzo.Code.Peras.SmallStep.C_CastVote_770 v25 v26 v29 ->
            case coe v29 of
              MAlonzo.Code.Peras.SmallStep.C_honest_672 v31 v33 v34 v35 v38 v40 v41 ->
                let v42 =
                      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                        (coe v10)
                        (coe v25)
                 in coe
                      ( case coe v42 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v43 v44 ->
                            if coe v43
                              then
                                coe
                                  seq
                                  (coe v44)
                                  ( coe
                                      MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
                                      ( coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_extendable'45'votes_322
                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                  (coe v5)
                                              )
                                              v12
                                              ( coe
                                                  MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                  ( coe
                                                      MAlonzo.Code.Peras.Numbering.C_MkRoundNumber_32
                                                      ( coe
                                                          MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                                          ( coe
                                                              MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.Params.d_T_24
                                                              (coe v4)
                                                          )
                                                      )
                                                  )
                                                  (coe v25)
                                                  (coe v33)
                                                  ( coe
                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                      v2
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.du_tip_172
                                                          (coe v0)
                                                          (coe v2)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                              v5
                                                              ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Params.d_L_30
                                                                      (coe v4)
                                                                  )
                                                              )
                                                              v31
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                  (coe v5)
                                                              )
                                                              v31
                                                              ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Params.d_L_30
                                                                      (coe v4)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                  )
                                                  (coe v34)
                                              )
                                          )
                                      )
                                      ( coe
                                          du_knowledge'45'propagation_896
                                          (coe v0)
                                          (coe v1)
                                          (coe v2)
                                          (coe v3)
                                          (coe v4)
                                          (coe v5)
                                          (coe v6)
                                          (coe v7)
                                          (coe v8)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                  (coe v9)
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                  v25
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                          v5
                                                          v31
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                  (coe v4)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                              (coe v25)
                                                              (coe v33)
                                                              ( let v45 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v46 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.Params.d_L_30
                                                                                        (coe v4)
                                                                                    )
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v45 v46)
                                                                      )
                                                              )
                                                              (coe v34)
                                                          )
                                                      )
                                                  )
                                                  ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                      ( coe
                                                          MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                          ( coe
                                                              ( \v45 v46 ->
                                                                  coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                    (coe v45)
                                                                    (coe v46)
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                                (coe v4)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                            )
                                                                            (coe v25)
                                                                            (coe v33)
                                                                            ( let v47 =
                                                                                    MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                      (coe v2)
                                                                               in coe
                                                                                    ( let v48 =
                                                                                            coe
                                                                                              MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                              (coe v0)
                                                                                              (coe v2)
                                                                                              (coe v5)
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                      ( coe
                                                                                                          v9
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.Params.d_L_30
                                                                                                      ( coe
                                                                                                          v4
                                                                                                      )
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  v31
                                                                                              )
                                                                                       in coe (coe v47 v48)
                                                                                    )
                                                                            )
                                                                            (coe v34)
                                                                        )
                                                                    )
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                    )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_filter_740
                                                          ( coe
                                                              ( \v45 ->
                                                                  coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                        (coe v25)
                                                                        ( coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe v45)
                                                                        )
                                                                    )
                                                              )
                                                          )
                                                          (coe v8)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                              (coe v4)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                          )
                                                          (coe v25)
                                                          (coe v33)
                                                          ( let v45 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v46 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Params.d_L_30
                                                                                    (coe v4)
                                                                                )
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v45 v46)
                                                                  )
                                                          )
                                                          (coe v34)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_history_538
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                  (coe v9)
                                              )
                                          )
                                          (coe v10)
                                          (coe v11)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                              v5
                                              v12
                                              ( coe
                                                  MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                  ( coe
                                                      MAlonzo.Code.Peras.Numbering.C_MkRoundNumber_32
                                                      ( coe
                                                          MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                                          ( coe
                                                              MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.Params.d_T_24
                                                              (coe v4)
                                                          )
                                                      )
                                                  )
                                                  (coe v25)
                                                  (coe v33)
                                                  ( coe
                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                      v2
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.du_tip_172
                                                          (coe v0)
                                                          (coe v2)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                              v5
                                                              ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Params.d_L_30
                                                                      (coe v4)
                                                                  )
                                                              )
                                                              v31
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                              ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                  (coe v5)
                                                              )
                                                              v31
                                                              ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Params.d_L_30
                                                                      (coe v4)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                  )
                                                  (coe v34)
                                              )
                                          )
                                          (coe v13)
                                          (coe v14)
                                          (coe v15)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                      (coe v9)
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                      MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                      v25
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                              v5
                                                              v31
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                      (coe v4)
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                  )
                                                                  (coe v25)
                                                                  (coe v33)
                                                                  ( let v45 =
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            (coe v2)
                                                                     in coe
                                                                          ( let v46 =
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                    (coe v0)
                                                                                    (coe v2)
                                                                                    (coe v5)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                        ( coe
                                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                            (coe v9)
                                                                                        )
                                                                                        ( coe
                                                                                            MAlonzo.Code.Peras.Params.d_L_30
                                                                                            (coe v4)
                                                                                        )
                                                                                    )
                                                                                    (coe v31)
                                                                             in coe (coe v45 v46)
                                                                          )
                                                                  )
                                                                  (coe v34)
                                                              )
                                                          )
                                                      )
                                                      ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_map_22
                                                          ( coe
                                                              MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                              ( coe
                                                                  ( \v45 v46 ->
                                                                      coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                        (coe v45)
                                                                        (coe v46)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                                    (coe v4)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                )
                                                                                (coe v25)
                                                                                (coe v33)
                                                                                ( let v47 =
                                                                                        MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                          ( coe
                                                                                              v2
                                                                                          )
                                                                                   in coe
                                                                                        ( let v48 =
                                                                                                coe
                                                                                                  MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                                  ( coe
                                                                                                      v0
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v2
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v5
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                          ( coe
                                                                                                              v9
                                                                                                          )
                                                                                                      )
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.Params.d_L_30
                                                                                                          ( coe
                                                                                                              v4
                                                                                                          )
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v31
                                                                                                  )
                                                                                           in coe
                                                                                                (coe v47 v48)
                                                                                        )
                                                                                )
                                                                                (coe v34)
                                                                            )
                                                                        )
                                                                        ( coe
                                                                            MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                        )
                                                                  )
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Base.du_filter_740
                                                              ( coe
                                                                  ( \v45 ->
                                                                      coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                        ( coe
                                                                            MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                            (coe v25)
                                                                            ( coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                (coe v45)
                                                                            )
                                                                        )
                                                                  )
                                                              )
                                                              (coe v8)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                  (coe v4)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                              (coe v25)
                                                              (coe v33)
                                                              ( let v45 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v46 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.Params.d_L_30
                                                                                        (coe v4)
                                                                                    )
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v45 v46)
                                                                      )
                                                              )
                                                              (coe v34)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_history_538
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                      (coe v9)
                                                  )
                                              )
                                              (coe v16)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_CastVote_770
                                                  v25
                                                  (coe MAlonzo.Code.Peras.Block.C_Honest_30)
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_honest_672
                                                      v31
                                                      v33
                                                      v34
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                          ( coe
                                                              MAlonzo.Code.Peras.Numbering.C_MkRoundNumber_32
                                                              ( coe
                                                                  MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Params.d_T_24
                                                                      (coe v4)
                                                                  )
                                                              )
                                                          )
                                                          (coe v25)
                                                          (coe v33)
                                                          ( coe
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                              v2
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Chain.du_tip_172
                                                                  (coe v0)
                                                                  (coe v2)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                      v5
                                                                      ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.Params.d_L_30
                                                                              (coe v4)
                                                                          )
                                                                      )
                                                                      v31
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                          (coe v5)
                                                                      )
                                                                      v31
                                                                      ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          ( coe
                                                                              MAlonzo.Code.Peras.Params.d_L_30
                                                                              (coe v4)
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                          (coe v34)
                                                      )
                                                      v38
                                                      v40
                                                      v41
                                                  )
                                              )
                                          )
                                          (coe v24)
                                          (coe v18)
                                      )
                                      (coe v19)
                                  )
                              else
                                coe
                                  seq
                                  (coe v44)
                                  ( coe
                                      du_knowledge'45'propagation_896
                                      (coe v0)
                                      (coe v1)
                                      (coe v2)
                                      (coe v3)
                                      (coe v4)
                                      (coe v5)
                                      (coe v6)
                                      (coe v7)
                                      (coe v8)
                                      ( coe
                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                              (coe v9)
                                          )
                                          ( coe
                                              MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                              MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                              v25
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                      v5
                                                      v31
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                              (coe v4)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                          )
                                                          (coe v25)
                                                          (coe v33)
                                                          ( let v45 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v46 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Params.d_L_30
                                                                                    (coe v4)
                                                                                )
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v45 v46)
                                                                  )
                                                          )
                                                          (coe v34)
                                                      )
                                                  )
                                              )
                                              ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du_map_22
                                                  ( coe
                                                      MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                      ( coe
                                                          ( \v45 v46 ->
                                                              coe
                                                                MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                (coe v45)
                                                                (coe v46)
                                                                ( coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                            (coe v4)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                        )
                                                                        (coe v25)
                                                                        (coe v33)
                                                                        ( let v47 =
                                                                                MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                  (coe v2)
                                                                           in coe
                                                                                ( let v48 =
                                                                                        coe
                                                                                          MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                          (coe v0)
                                                                                          (coe v2)
                                                                                          (coe v5)
                                                                                          ( coe
                                                                                              MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                  ( coe
                                                                                                      v9
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.Params.d_L_30
                                                                                                  ( coe
                                                                                                      v4
                                                                                                  )
                                                                                              )
                                                                                          )
                                                                                          (coe v31)
                                                                                   in coe (coe v47 v48)
                                                                                )
                                                                        )
                                                                        (coe v34)
                                                                    )
                                                                )
                                                                ( coe
                                                                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                )
                                                          )
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_filter_740
                                                      ( coe
                                                          ( \v45 ->
                                                              coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                ( coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                    (coe v25)
                                                                    ( coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                        (coe v45)
                                                                    )
                                                                )
                                                          )
                                                      )
                                                      (coe v8)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                  ( coe
                                                      MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                          (coe v4)
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                              (coe v9)
                                                          )
                                                      )
                                                      (coe v25)
                                                      (coe v33)
                                                      ( let v45 =
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                (coe v2)
                                                         in coe
                                                              ( let v46 =
                                                                      coe
                                                                        MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                        (coe v0)
                                                                        (coe v2)
                                                                        (coe v5)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Params.d_L_30
                                                                                (coe v4)
                                                                            )
                                                                        )
                                                                        (coe v31)
                                                                 in coe (coe v45 v46)
                                                              )
                                                      )
                                                      (coe v34)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_history_538
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                              (coe v9)
                                          )
                                      )
                                      (coe v10)
                                      (coe v11)
                                      (coe v12)
                                      (coe v13)
                                      (coe v14)
                                      (coe v15)
                                      ( coe
                                          MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                  (coe v9)
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                  v25
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_addVote_414
                                                          v5
                                                          v31
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                  (coe v4)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                              (coe v25)
                                                              (coe v33)
                                                              ( let v45 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v46 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.Params.d_L_30
                                                                                        (coe v4)
                                                                                    )
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v45 v46)
                                                                      )
                                                              )
                                                              (coe v34)
                                                          )
                                                      )
                                                  )
                                                  ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                      ( coe
                                                          MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                          ( coe
                                                              ( \v45 v46 ->
                                                                  coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                    (coe v45)
                                                                    (coe v46)
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                                                (coe v4)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                            )
                                                                            (coe v25)
                                                                            (coe v33)
                                                                            ( let v47 =
                                                                                    MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                      (coe v2)
                                                                               in coe
                                                                                    ( let v48 =
                                                                                            coe
                                                                                              MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                              (coe v0)
                                                                                              (coe v2)
                                                                                              (coe v5)
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                      ( coe
                                                                                                          v9
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.Params.d_L_30
                                                                                                      ( coe
                                                                                                          v4
                                                                                                      )
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  v31
                                                                                              )
                                                                                       in coe (coe v47 v48)
                                                                                    )
                                                                            )
                                                                            (coe v34)
                                                                        )
                                                                    )
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                    )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_filter_740
                                                          ( coe
                                                              ( \v45 ->
                                                                  coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                        (coe v25)
                                                                        ( coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe v45)
                                                                        )
                                                                    )
                                                              )
                                                          )
                                                          (coe v8)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_VoteMsg_66
                                                      ( coe
                                                          MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_v'45'round_130
                                                              (coe v4)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                          )
                                                          (coe v25)
                                                          (coe v33)
                                                          ( let v45 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v46 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Params.d_L_30
                                                                                    (coe v4)
                                                                                )
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v45 v46)
                                                                  )
                                                          )
                                                          (coe v34)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_history_538
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                  (coe v9)
                                              )
                                          )
                                          (coe v16)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_CastVote_770
                                              v25
                                              (coe MAlonzo.Code.Peras.Block.C_Honest_30)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_honest_672
                                                  v31
                                                  v33
                                                  v34
                                                  ( coe
                                                      MAlonzo.Code.Peras.Chain.C_MkVote_26
                                                      ( coe
                                                          MAlonzo.Code.Peras.Numbering.C_MkRoundNumber_32
                                                          ( coe
                                                              MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Numbering.d_getSlotNumber_8
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Params.d_T_24
                                                                  (coe v4)
                                                              )
                                                          )
                                                      )
                                                      (coe v25)
                                                      (coe v33)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.Params.d_L_30
                                                                          (coe v4)
                                                                      )
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.Numbering.d__earlierBy__12
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.Params.d_L_30
                                                                          (coe v4)
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      (coe v34)
                                                  )
                                                  v38
                                                  v40
                                                  v41
                                              )
                                          )
                                      )
                                      (coe v24)
                                      (coe v18)
                                      (coe v19)
                                  )
                          _ -> MAlonzo.RTE.mazUnreachableError
                      )
              _ -> MAlonzo.RTE.mazUnreachableError
          MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772 v25 v26 v29 ->
            case coe v29 of
              MAlonzo.Code.Peras.SmallStep.C_honest_708 v31 v33 v34 v35 v38 v39 ->
                let v40 =
                      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                        (coe v10)
                        (coe v25)
                 in coe
                      ( case coe v40 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v41 v42 ->
                            if coe v41
                              then
                                coe
                                  seq
                                  (coe v42)
                                  ( coe
                                      du_x'8759'xs'8838'ys'8594'xs'8838'ys_1660
                                      ( coe
                                          MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
                                          ( coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_extendable_316
                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                      (coe v5)
                                                  )
                                                  v12
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                              )
                                          )
                                          ( coe
                                              du_knowledge'45'propagation_896
                                              (coe v0)
                                              (coe v1)
                                              (coe v2)
                                              (coe v3)
                                              (coe v4)
                                              (coe v5)
                                              (coe v6)
                                              (coe v7)
                                              (coe v8)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                      (coe v9)
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                      MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                      v25
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                              v5
                                                              v31
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  (coe v25)
                                                                  ( let v43 =
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            (coe v2)
                                                                     in coe
                                                                          ( let v44 =
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                    (coe v0)
                                                                                    (coe v2)
                                                                                    (coe v5)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    (coe v31)
                                                                             in coe (coe v43 v44)
                                                                          )
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  )
                                                                  (coe v33)
                                                                  (coe v34)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                      v3
                                                                      ( coe
                                                                          v7
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          v25
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_map_22
                                                          ( coe
                                                              MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                              ( coe
                                                                  ( \v43 v44 ->
                                                                      coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                        (coe v43)
                                                                        (coe v44)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                (coe v25)
                                                                                ( let v45 =
                                                                                        MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                          ( coe
                                                                                              v2
                                                                                          )
                                                                                   in coe
                                                                                        ( let v46 =
                                                                                                coe
                                                                                                  MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                                  ( coe
                                                                                                      v0
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v2
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v5
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                      ( coe
                                                                                                          v9
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v31
                                                                                                  )
                                                                                           in coe
                                                                                                (coe v45 v46)
                                                                                        )
                                                                                )
                                                                                ( coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                )
                                                                                (coe v33)
                                                                                (coe v34)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                    v3
                                                                                    ( coe
                                                                                        v7
                                                                                        ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                            (coe v9)
                                                                                        )
                                                                                        v25
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                        ( coe
                                                                            MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                        )
                                                                  )
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Base.du_filter_740
                                                              ( coe
                                                                  ( \v43 ->
                                                                      coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                        ( coe
                                                                            MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                            (coe v25)
                                                                            ( coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                (coe v43)
                                                                            )
                                                                        )
                                                                  )
                                                              )
                                                              (coe v8)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              (coe v25)
                                                              ( let v43 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v44 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v43 v44)
                                                                      )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              )
                                                              (coe v33)
                                                              (coe v34)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v3
                                                                  ( coe
                                                                      v7
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      v25
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_history_538
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                      (coe v9)
                                                  )
                                              )
                                              (coe v10)
                                              (coe v11)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                  v5
                                                  v12
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                              )
                                              (coe v13)
                                              (coe v14)
                                              (coe v15)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                          MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                          v25
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                  v5
                                                                  v31
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      (coe v25)
                                                                      ( let v43 =
                                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                (coe v2)
                                                                         in coe
                                                                              ( let v44 =
                                                                                      coe
                                                                                        MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                        (coe v0)
                                                                                        (coe v2)
                                                                                        (coe v5)
                                                                                        ( coe
                                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                            (coe v9)
                                                                                        )
                                                                                        (coe v31)
                                                                                 in coe (coe v43 v44)
                                                                              )
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      )
                                                                      (coe v33)
                                                                      (coe v34)
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                          v3
                                                                          ( coe
                                                                              v7
                                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                  (coe v9)
                                                                              )
                                                                              v25
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                          ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                              (coe v9)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Base.du_map_22
                                                              ( coe
                                                                  MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                                  ( coe
                                                                      ( \v43 v44 ->
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                            (coe v43)
                                                                            (coe v44)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    (coe v25)
                                                                                    ( let v45 =
                                                                                            MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                              ( coe
                                                                                                  v2
                                                                                              )
                                                                                       in coe
                                                                                            ( let v46 =
                                                                                                    coe
                                                                                                      MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                                      ( coe
                                                                                                          v0
                                                                                                      )
                                                                                                      ( coe
                                                                                                          v2
                                                                                                      )
                                                                                                      ( coe
                                                                                                          v5
                                                                                                      )
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                          ( coe
                                                                                                              v9
                                                                                                          )
                                                                                                      )
                                                                                                      ( coe
                                                                                                          v31
                                                                                                      )
                                                                                               in coe
                                                                                                    ( coe
                                                                                                        v45
                                                                                                        v46
                                                                                                    )
                                                                                            )
                                                                                    )
                                                                                    ( coe
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    )
                                                                                    (coe v33)
                                                                                    (coe v34)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                        v3
                                                                                        ( coe
                                                                                            v7
                                                                                            ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                (coe v9)
                                                                                            )
                                                                                            v25
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                            ( coe
                                                                                MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                            )
                                                                      )
                                                                  )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Data.List.Base.du_filter_740
                                                                  ( coe
                                                                      ( \v43 ->
                                                                          coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                            ( coe
                                                                                MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                                (coe v25)
                                                                                ( coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                    (coe v43)
                                                                                )
                                                                            )
                                                                      )
                                                                  )
                                                                  (coe v8)
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                              (coe v9)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  (coe v25)
                                                                  ( let v43 =
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            (coe v2)
                                                                     in coe
                                                                          ( let v44 =
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                    (coe v0)
                                                                                    (coe v2)
                                                                                    (coe v5)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    (coe v31)
                                                                             in coe (coe v43 v44)
                                                                          )
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  )
                                                                  (coe v33)
                                                                  (coe v34)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                      v3
                                                                      ( coe
                                                                          v7
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          v25
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_history_538
                                                              (coe v9)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                          (coe v9)
                                                      )
                                                  )
                                                  (coe v16)
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772
                                                      v25
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_Honest_30
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_honest_708
                                                          v31
                                                          v33
                                                          v34
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              (coe v25)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v2
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Chain.du_tip_172
                                                                      (coe v0)
                                                                      (coe v2)
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                          v5
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          v31
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                              (coe v5)
                                                                          )
                                                                          v31
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              )
                                                              (coe v33)
                                                              (coe v34)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v3
                                                                  ( coe
                                                                      v7
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      v25
                                                                  )
                                                              )
                                                          )
                                                          v38
                                                          v39
                                                      )
                                                  )
                                              )
                                              (coe v24)
                                              (coe v18)
                                          )
                                      )
                                      v19
                                  )
                              else
                                coe
                                  seq
                                  (coe v42)
                                  ( coe
                                      du_knowledge'45'propagation_896
                                      (coe v0)
                                      (coe v1)
                                      (coe v2)
                                      (coe v3)
                                      (coe v4)
                                      (coe v5)
                                      (coe v6)
                                      (coe v7)
                                      (coe v8)
                                      ( coe
                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                              (coe v9)
                                          )
                                          ( coe
                                              MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                              MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                              v25
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                      v5
                                                      v31
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                              (coe v9)
                                                          )
                                                          (coe v25)
                                                          ( let v43 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v44 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v43 v44)
                                                                  )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          )
                                                          (coe v33)
                                                          (coe v34)
                                                          ( coe
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                              v3
                                                              ( coe
                                                                  v7
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v25
                                                              )
                                                          )
                                                      )
                                                  )
                                              )
                                              ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du_map_22
                                                  ( coe
                                                      MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                      ( coe
                                                          ( \v43 v44 ->
                                                              coe
                                                                MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                (coe v43)
                                                                (coe v44)
                                                                ( coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                            (coe v9)
                                                                        )
                                                                        (coe v25)
                                                                        ( let v45 =
                                                                                MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                  (coe v2)
                                                                           in coe
                                                                                ( let v46 =
                                                                                        coe
                                                                                          MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                          (coe v0)
                                                                                          (coe v2)
                                                                                          (coe v5)
                                                                                          ( coe
                                                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                              (coe v9)
                                                                                          )
                                                                                          (coe v31)
                                                                                   in coe (coe v45 v46)
                                                                                )
                                                                        )
                                                                        ( coe
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        )
                                                                        (coe v33)
                                                                        (coe v34)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            v3
                                                                            ( coe
                                                                                v7
                                                                                ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                v25
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                                ( coe
                                                                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                )
                                                          )
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_filter_740
                                                      ( coe
                                                          ( \v43 ->
                                                              coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                ( coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                    (coe v25)
                                                                    ( coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                        (coe v43)
                                                                    )
                                                                )
                                                          )
                                                      )
                                                      (coe v8)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( let v43 =
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                (coe v2)
                                                         in coe
                                                              ( let v44 =
                                                                      coe
                                                                        MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                        (coe v0)
                                                                        (coe v2)
                                                                        (coe v5)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                            (coe v9)
                                                                        )
                                                                        (coe v31)
                                                                 in coe (coe v43 v44)
                                                              )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_history_538
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                              (coe v9)
                                          )
                                      )
                                      (coe v10)
                                      (coe v11)
                                      (coe v12)
                                      (coe v13)
                                      (coe v14)
                                      (coe v15)
                                      ( coe
                                          MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                  (coe v9)
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                  v25
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                          v5
                                                          v31
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              (coe v25)
                                                              ( let v43 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v44 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v43 v44)
                                                                      )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              )
                                                              (coe v33)
                                                              (coe v34)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v3
                                                                  ( coe
                                                                      v7
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      v25
                                                                  )
                                                              )
                                                          )
                                                      )
                                                  )
                                                  ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                      ( coe
                                                          MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                          ( coe
                                                              ( \v43 v44 ->
                                                                  coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                    (coe v43)
                                                                    (coe v44)
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            (coe v25)
                                                                            ( let v45 =
                                                                                    MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                      (coe v2)
                                                                               in coe
                                                                                    ( let v46 =
                                                                                            coe
                                                                                              MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                              (coe v0)
                                                                                              (coe v2)
                                                                                              (coe v5)
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                  ( coe
                                                                                                      v9
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  v31
                                                                                              )
                                                                                       in coe (coe v45 v46)
                                                                                    )
                                                                            )
                                                                            ( coe
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            )
                                                                            (coe v33)
                                                                            (coe v34)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                v3
                                                                                ( coe
                                                                                    v7
                                                                                    ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    v25
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                    )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_filter_740
                                                          ( coe
                                                              ( \v43 ->
                                                                  coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                        (coe v25)
                                                                        ( coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe v43)
                                                                        )
                                                                    )
                                                              )
                                                          )
                                                          (coe v8)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                              (coe v9)
                                                          )
                                                          (coe v25)
                                                          ( let v43 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v44 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v43 v44)
                                                                  )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          )
                                                          (coe v33)
                                                          (coe v34)
                                                          ( coe
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                              v3
                                                              ( coe
                                                                  v7
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v25
                                                              )
                                                          )
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_history_538
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                  (coe v9)
                                              )
                                          )
                                          (coe v16)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772
                                              v25
                                              (coe MAlonzo.Code.Peras.Block.C_Honest_30)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_honest_708
                                                  v31
                                                  v33
                                                  v34
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                                  v38
                                                  v39
                                              )
                                          )
                                      )
                                      (coe v24)
                                      (coe v18)
                                      (coe v19)
                                  )
                          _ -> MAlonzo.RTE.mazUnreachableError
                      )
              MAlonzo.Code.Peras.SmallStep.C_honest'45'cooldown_752 v31 v33 v34 v35 v38 v39 v41 v42 ->
                let v43 =
                      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                        (coe v10)
                        (coe v25)
                 in coe
                      ( case coe v43 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v44 v45 ->
                            if coe v44
                              then
                                coe
                                  seq
                                  (coe v45)
                                  ( coe
                                      du_x'8759'xs'8838'ys'8594'xs'8838'ys_1824
                                      ( coe
                                          MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
                                          ( coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_extendable_316
                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                      (coe v5)
                                                  )
                                                  v12
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                              )
                                          )
                                          ( coe
                                              du_knowledge'45'propagation_896
                                              (coe v0)
                                              (coe v1)
                                              (coe v2)
                                              (coe v3)
                                              (coe v4)
                                              (coe v5)
                                              (coe v6)
                                              (coe v7)
                                              (coe v8)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                      (coe v9)
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                      MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                      v25
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                              v5
                                                              v31
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  (coe v25)
                                                                  ( let v46 =
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            (coe v2)
                                                                     in coe
                                                                          ( let v47 =
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                    (coe v0)
                                                                                    (coe v2)
                                                                                    (coe v5)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    (coe v31)
                                                                             in coe (coe v46 v47)
                                                                          )
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  )
                                                                  (coe v33)
                                                                  (coe v34)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                      v3
                                                                      ( coe
                                                                          v7
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          v25
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_map_22
                                                          ( coe
                                                              MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                              ( coe
                                                                  ( \v46 v47 ->
                                                                      coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                        (coe v46)
                                                                        (coe v47)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                (coe v25)
                                                                                ( let v48 =
                                                                                        MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                          ( coe
                                                                                              v2
                                                                                          )
                                                                                   in coe
                                                                                        ( let v49 =
                                                                                                coe
                                                                                                  MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                                  ( coe
                                                                                                      v0
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v2
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v5
                                                                                                  )
                                                                                                  ( coe
                                                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                      ( coe
                                                                                                          v9
                                                                                                      )
                                                                                                  )
                                                                                                  ( coe
                                                                                                      v31
                                                                                                  )
                                                                                           in coe
                                                                                                (coe v48 v49)
                                                                                        )
                                                                                )
                                                                                ( coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                )
                                                                                (coe v33)
                                                                                (coe v34)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                    v3
                                                                                    ( coe
                                                                                        v7
                                                                                        ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                            (coe v9)
                                                                                        )
                                                                                        v25
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                        ( coe
                                                                            MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                        )
                                                                  )
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Base.du_filter_740
                                                              ( coe
                                                                  ( \v46 ->
                                                                      coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                        ( coe
                                                                            MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                            (coe v25)
                                                                            ( coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                (coe v46)
                                                                            )
                                                                        )
                                                                  )
                                                              )
                                                              (coe v8)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              (coe v25)
                                                              ( let v46 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v47 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v46 v47)
                                                                      )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              )
                                                              (coe v33)
                                                              (coe v34)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v3
                                                                  ( coe
                                                                      v7
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      v25
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_history_538
                                                          (coe v9)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                      (coe v9)
                                                  )
                                              )
                                              (coe v10)
                                              (coe v11)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                  v5
                                                  v12
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                              )
                                              (coe v13)
                                              (coe v14)
                                              (coe v15)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                          MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                          v25
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                                  v5
                                                                  v31
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      (coe v25)
                                                                      ( let v46 =
                                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                (coe v2)
                                                                         in coe
                                                                              ( let v47 =
                                                                                      coe
                                                                                        MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                        (coe v0)
                                                                                        (coe v2)
                                                                                        (coe v5)
                                                                                        ( coe
                                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                            (coe v9)
                                                                                        )
                                                                                        (coe v31)
                                                                                 in coe (coe v46 v47)
                                                                              )
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                      )
                                                                      (coe v33)
                                                                      (coe v34)
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                          v3
                                                                          ( coe
                                                                              v7
                                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                  (coe v9)
                                                                              )
                                                                              v25
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                          ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                              (coe v9)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                          ( coe
                                                              MAlonzo.Code.Data.List.Base.du_map_22
                                                              ( coe
                                                                  MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                                  ( coe
                                                                      ( \v46 v47 ->
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                            (coe v46)
                                                                            (coe v47)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    (coe v25)
                                                                                    ( let v48 =
                                                                                            MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                              ( coe
                                                                                                  v2
                                                                                              )
                                                                                       in coe
                                                                                            ( let v49 =
                                                                                                    coe
                                                                                                      MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                                      ( coe
                                                                                                          v0
                                                                                                      )
                                                                                                      ( coe
                                                                                                          v2
                                                                                                      )
                                                                                                      ( coe
                                                                                                          v5
                                                                                                      )
                                                                                                      ( coe
                                                                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                          ( coe
                                                                                                              v9
                                                                                                          )
                                                                                                      )
                                                                                                      ( coe
                                                                                                          v31
                                                                                                      )
                                                                                               in coe
                                                                                                    ( coe
                                                                                                        v48
                                                                                                        v49
                                                                                                    )
                                                                                            )
                                                                                    )
                                                                                    ( coe
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    )
                                                                                    (coe v33)
                                                                                    (coe v34)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                        v3
                                                                                        ( coe
                                                                                            v7
                                                                                            ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                (coe v9)
                                                                                            )
                                                                                            v25
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                            ( coe
                                                                                MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                            )
                                                                      )
                                                                  )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Data.List.Base.du_filter_740
                                                                  ( coe
                                                                      ( \v46 ->
                                                                          coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                            ( coe
                                                                                MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                                (coe v25)
                                                                                ( coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                    (coe v46)
                                                                                )
                                                                            )
                                                                      )
                                                                  )
                                                                  (coe v8)
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                              (coe v9)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  (coe v25)
                                                                  ( let v46 =
                                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            (coe v2)
                                                                     in coe
                                                                          ( let v47 =
                                                                                  coe
                                                                                    MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                    (coe v0)
                                                                                    (coe v2)
                                                                                    (coe v5)
                                                                                    ( coe
                                                                                        MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    (coe v31)
                                                                             in coe (coe v46 v47)
                                                                          )
                                                                  )
                                                                  ( coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  )
                                                                  (coe v33)
                                                                  (coe v34)
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                      v3
                                                                      ( coe
                                                                          v7
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          v25
                                                                      )
                                                                  )
                                                              )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_history_538
                                                              (coe v9)
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                          (coe v9)
                                                      )
                                                  )
                                                  (coe v16)
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772
                                                      v25
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_Honest_30
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.C_honest'45'cooldown_752
                                                          v31
                                                          v33
                                                          v34
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              (coe v25)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v2
                                                                  ( coe
                                                                      MAlonzo.Code.Peras.Chain.du_tip_172
                                                                      (coe v0)
                                                                      (coe v2)
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                          v5
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                          v31
                                                                      )
                                                                      ( coe
                                                                          MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                              (coe v5)
                                                                          )
                                                                          v31
                                                                          ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                              (coe v9)
                                                                          )
                                                                      )
                                                                  )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              )
                                                              (coe v33)
                                                              (coe v34)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v3
                                                                  ( coe
                                                                      v7
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      v25
                                                                  )
                                                              )
                                                          )
                                                          v38
                                                          v39
                                                          v41
                                                          v42
                                                      )
                                                  )
                                              )
                                              (coe v24)
                                              (coe v18)
                                          )
                                      )
                                      v19
                                  )
                              else
                                coe
                                  seq
                                  (coe v45)
                                  ( coe
                                      du_knowledge'45'propagation_896
                                      (coe v0)
                                      (coe v1)
                                      (coe v2)
                                      (coe v3)
                                      (coe v4)
                                      (coe v5)
                                      (coe v6)
                                      (coe v7)
                                      (coe v8)
                                      ( coe
                                          MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                              (coe v9)
                                          )
                                          ( coe
                                              MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                              MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                              v25
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                      v5
                                                      v31
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                              (coe v9)
                                                          )
                                                          (coe v25)
                                                          ( let v46 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v47 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v46 v47)
                                                                  )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          )
                                                          (coe v33)
                                                          (coe v34)
                                                          ( coe
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                              v3
                                                              ( coe
                                                                  v7
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v25
                                                              )
                                                          )
                                                      )
                                                  )
                                              )
                                              ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du_map_22
                                                  ( coe
                                                      MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                      ( coe
                                                          ( \v46 v47 ->
                                                              coe
                                                                MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                (coe v46)
                                                                (coe v47)
                                                                ( coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                            (coe v9)
                                                                        )
                                                                        (coe v25)
                                                                        ( let v48 =
                                                                                MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                  (coe v2)
                                                                           in coe
                                                                                ( let v49 =
                                                                                        coe
                                                                                          MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                          (coe v0)
                                                                                          (coe v2)
                                                                                          (coe v5)
                                                                                          ( coe
                                                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                              (coe v9)
                                                                                          )
                                                                                          (coe v31)
                                                                                   in coe (coe v48 v49)
                                                                                )
                                                                        )
                                                                        ( coe
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        )
                                                                        (coe v33)
                                                                        (coe v34)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                            v3
                                                                            ( coe
                                                                                v7
                                                                                ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                v25
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                                ( coe
                                                                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                )
                                                          )
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_filter_740
                                                      ( coe
                                                          ( \v46 ->
                                                              coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                ( coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                    (coe v25)
                                                                    ( coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                        (coe v46)
                                                                    )
                                                                )
                                                          )
                                                      )
                                                      (coe v8)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( let v46 =
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                (coe v2)
                                                         in coe
                                                              ( let v47 =
                                                                      coe
                                                                        MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                        (coe v0)
                                                                        (coe v2)
                                                                        (coe v5)
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                            (coe v9)
                                                                        )
                                                                        (coe v31)
                                                                 in coe (coe v46 v47)
                                                              )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_history_538
                                                  (coe v9)
                                              )
                                          )
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                              (coe v9)
                                          )
                                      )
                                      (coe v10)
                                      (coe v11)
                                      (coe v12)
                                      (coe v13)
                                      (coe v14)
                                      (coe v15)
                                      ( coe
                                          MAlonzo.Code.Peras.SmallStep.du_'8605''8728''8605''8902'_792
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_'10214'_'44'_'44'_'44'_'44'_'10215'_542
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                  (coe v9)
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.Tree.AVL.Map.du_insert_202
                                                  MAlonzo.Code.Peras.Block.d_PartyIdO_6
                                                  v25
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_'10218'_'10219'_452
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_extendTree_408
                                                          v5
                                                          v31
                                                          ( coe
                                                              MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              (coe v25)
                                                              ( let v46 =
                                                                      MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                        (coe v2)
                                                                 in coe
                                                                      ( let v47 =
                                                                              coe
                                                                                MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                (coe v0)
                                                                                (coe v2)
                                                                                (coe v5)
                                                                                ( coe
                                                                                    MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                    (coe v9)
                                                                                )
                                                                                (coe v31)
                                                                         in coe (coe v46 v47)
                                                                      )
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              )
                                                              (coe v33)
                                                              (coe v34)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                  v3
                                                                  ( coe
                                                                      v7
                                                                      ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                          (coe v9)
                                                                      )
                                                                      v25
                                                                  )
                                                              )
                                                          )
                                                      )
                                                  )
                                                  ( MAlonzo.Code.Peras.SmallStep.d_stateMap_534
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__62
                                                  ( coe
                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                      ( coe
                                                          MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                                          ( coe
                                                              ( \v46 v47 ->
                                                                  coe
                                                                    MAlonzo.Code.Peras.SmallStep.C_'10629'_'44'_'44'_'44'_'10630'_100
                                                                    (coe v46)
                                                                    (coe v47)
                                                                    ( coe
                                                                        MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                                        ( coe
                                                                            MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            (coe v25)
                                                                            ( let v48 =
                                                                                    MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                      (coe v2)
                                                                               in coe
                                                                                    ( let v49 =
                                                                                            coe
                                                                                              MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                                              (coe v0)
                                                                                              (coe v2)
                                                                                              (coe v5)
                                                                                              ( coe
                                                                                                  MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                                  ( coe
                                                                                                      v9
                                                                                                  )
                                                                                              )
                                                                                              ( coe
                                                                                                  v31
                                                                                              )
                                                                                       in coe (coe v48 v49)
                                                                                    )
                                                                            )
                                                                            ( coe
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            )
                                                                            (coe v33)
                                                                            (coe v34)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                                v3
                                                                                ( coe
                                                                                    v7
                                                                                    ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                        (coe v9)
                                                                                    )
                                                                                    v25
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                                    )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Data.List.Base.du_filter_740
                                                          ( coe
                                                              ( \v46 ->
                                                                  coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_68
                                                                    ( coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d__'8799'__2558
                                                                        (coe v25)
                                                                        ( coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe v46)
                                                                        )
                                                                    )
                                                              )
                                                          )
                                                          (coe v8)
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_messages_536
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.C_BlockMsg_64
                                                      ( coe
                                                          MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                          ( coe
                                                              MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                              (coe v9)
                                                          )
                                                          (coe v25)
                                                          ( let v46 =
                                                                  MAlonzo.Code.Peras.Crypto.d_hash_40
                                                                    (coe v2)
                                                             in coe
                                                                  ( let v47 =
                                                                          coe
                                                                            MAlonzo.Code.Peras.SmallStep.du_tipBest_422
                                                                            (coe v0)
                                                                            (coe v2)
                                                                            (coe v5)
                                                                            ( coe
                                                                                MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                                (coe v9)
                                                                            )
                                                                            (coe v31)
                                                                     in coe (coe v46 v47)
                                                                  )
                                                          )
                                                          ( coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          )
                                                          (coe v33)
                                                          (coe v34)
                                                          ( coe
                                                              MAlonzo.Code.Peras.Crypto.d_hash_40
                                                              v3
                                                              ( coe
                                                                  v7
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v25
                                                              )
                                                          )
                                                      )
                                                  )
                                                  ( coe
                                                      MAlonzo.Code.Peras.SmallStep.d_history_538
                                                      (coe v9)
                                                  )
                                              )
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.d_adversarialState_540
                                                  (coe v9)
                                              )
                                          )
                                          (coe v16)
                                          ( coe
                                              MAlonzo.Code.Peras.SmallStep.C_CreateBlock_772
                                              v25
                                              (coe MAlonzo.Code.Peras.Block.C_Honest_30)
                                              ( coe
                                                  MAlonzo.Code.Peras.SmallStep.C_honest'45'cooldown_752
                                                  v31
                                                  v33
                                                  v34
                                                  ( coe
                                                      MAlonzo.Code.Peras.Block.C_MkBlock_110
                                                      ( coe
                                                          MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                          (coe v9)
                                                      )
                                                      (coe v25)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v2
                                                          ( coe
                                                              MAlonzo.Code.Peras.Chain.du_tip_172
                                                              (coe v0)
                                                              (coe v2)
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_bestChain_412
                                                                  v5
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                                  v31
                                                              )
                                                              ( coe
                                                                  MAlonzo.Code.Peras.SmallStep.d_valid_328
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_is'45'TreeType_420
                                                                      (coe v5)
                                                                  )
                                                                  v31
                                                                  ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                      (coe v9)
                                                                  )
                                                              )
                                                          )
                                                      )
                                                      ( coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      )
                                                      (coe v33)
                                                      (coe v34)
                                                      ( coe
                                                          MAlonzo.Code.Peras.Crypto.d_hash_40
                                                          v3
                                                          ( coe
                                                              v7
                                                              ( MAlonzo.Code.Peras.SmallStep.d_clock_532
                                                                  (coe v9)
                                                              )
                                                              v25
                                                          )
                                                      )
                                                  )
                                                  v38
                                                  v39
                                                  v41
                                                  v42
                                              )
                                          )
                                      )
                                      (coe v24)
                                      (coe v18)
                                      (coe v19)
                                  )
                          _ -> MAlonzo.RTE.mazUnreachableError
                      )
              _ -> MAlonzo.RTE.mazUnreachableError
          MAlonzo.Code.Peras.SmallStep.C_NextSlot_774 v26 ->
            coe
              ( \v27 ->
                  coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_38
              )
          _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError

-- Peras.SmallStep.Properties._._._.x∷xs⊆ys→xs⊆ys
d_x'8759'xs'8838'ys'8594'xs'8838'ys_1660 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_x'8759'xs'8838'ys'8594'xs'8838'ys_1660
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
  ~v21
  ~v22
  ~v23
  ~v24
  ~v25
  ~v26
  ~v27
  ~v28
  ~v29
  ~v30
  ~v31
  ~v32
  ~v33
  ~v34
  ~v35
  ~v36
  ~v37
  ~v38
  ~v39
  ~v40
  ~v41
  ~v42
  ~v43
  ~v44 =
    du_x'8759'xs'8838'ys'8594'xs'8838'ys_1660
du_x'8759'xs'8838'ys'8594'xs'8838'ys_1660 ::
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_x'8759'xs'8838'ys'8594'xs'8838'ys_1660 =
  coe
    MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
    ( \v0 ->
        coe
          MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
    )

-- Peras.SmallStep.Properties._._._.x∷xs⊆ys→xs⊆ys
d_x'8759'xs'8838'ys'8594'xs'8838'ys_1824 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
  MAlonzo.Code.Peras.SmallStep.T_TreeType_386 ->
  () ->
  AgdaAny ->
  ( MAlonzo.Code.Peras.Numbering.T_SlotNumber_4 ->
    Integer ->
    [MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6]
  ) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  MAlonzo.Code.Peras.SmallStep.T_State'7501'_520 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Peras.Block.T_Honesty_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  AgdaAny ->
  MAlonzo.Code.Peras.Crypto.T_LeadershipProof_56 ->
  MAlonzo.Code.Peras.Crypto.T_Signature_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  ( MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
  ) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Peras.SmallStep.T__'8605''8902'__776 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  [MAlonzo.Code.Peras.Block.T_Block_62] ->
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_x'8759'xs'8838'ys'8594'xs'8838'ys_1824
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
  ~v21
  ~v22
  ~v23
  ~v24
  ~v25
  ~v26
  ~v27
  ~v28
  ~v29
  ~v30
  ~v31
  ~v32
  ~v33
  ~v34
  ~v35
  ~v36
  ~v37
  ~v38
  ~v39
  ~v40
  ~v41
  ~v42
  ~v43
  ~v44
  ~v45
  ~v46
  ~v47 =
    du_x'8759'xs'8838'ys'8594'xs'8838'ys_1824
du_x'8759'xs'8838'ys'8594'xs'8838'ys_1824 ::
  ( MAlonzo.Code.Peras.Block.T_Block_62 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
    MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
  ) ->
  MAlonzo.Code.Peras.Block.T_Block_62 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_x'8759'xs'8838'ys'8594'xs'8838'ys_1824 =
  coe
    MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_'8838''45'trans_94
    ( \v0 ->
        coe
          MAlonzo.Code.Data.List.Relation.Binary.Subset.Propositional.Properties.du_xs'8838'x'8759'xs_228
    )

-- Peras.SmallStep.Properties._._.luckySlots
d_luckySlots_1858 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.luckySlots"

-- Peras.SmallStep.Properties._._.superSlots
d_superSlots_1860 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.superSlots"

-- Peras.SmallStep.Properties._._.adversarialSlots
d_adversarialSlots_1862 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.adversarialSlots"

-- Peras.SmallStep.Properties._._.chain-growth
d_chain'45'growth_1890 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.chain-growth"

-- Peras.SmallStep.Properties._._.common-prefix
d_common'45'prefix_1910 =
  error
    "MAlonzo Runtime Error: postulate evaluated: Peras.SmallStep.Properties._._.common-prefix"
