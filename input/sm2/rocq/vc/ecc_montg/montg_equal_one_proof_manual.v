Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_equal_one_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_equal_one_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Import Snaive_C_Rules.
Local Open Scope sac.

Lemma proof_of_montg_equal_one_return_wit_1_split_goal_1 : montg_equal_one_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite !Z.lor_eq_0_iff, !Z.lxor_eq_0_iff in PreH9.
  destruct PreH9 as (((H0 & H1) & H2) & H3).
  subst x0; subst x1; subst x2; subst x3.
  lia.
Qed.

Lemma proof_of_montg_equal_one_return_wit_1_split_goal_spatial : montg_equal_one_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (proj1
       (u256_limb_diff_eq_zero_iff__eq
          x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3)
       PreH9) as [H0 [H1 [H2 H3]]].
  subst x0; subst x1; subst x2; subst x3.
  unfold store_montg_one, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2.
  split_pure_spatial.
  - cancel (((&( "MONTG_ONE" )) + (0 * sizeof(UINT64))) # UInt64 |-> x0_2).
    cancel (((&( "MONTG_ONE" )) + (1 * sizeof(UINT64))) # UInt64 |-> x1_2).
    cancel (((&( "MONTG_ONE" )) + (2 * sizeof(UINT64))) # UInt64 |-> x2_2).
    cancel (((&( "MONTG_ONE" )) + (3 * sizeof(UINT64))) # UInt64 |-> x3_2).
  - dump_pre_spatial.
    lia.
Qed.

Lemma proof_of_montg_equal_one_return_wit_1 : montg_equal_one_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_montg_equal_one_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_montg_equal_one_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_montg_equal_one_return_wit_2_split_goal_1 : montg_equal_one_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  intro HA.
  pose proof
    (u256_of_limbs_injective
       x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
       (conj PreH27 PreH26) (conj PreH25 PreH24)
       (conj PreH23 PreH22) (conj PreH21 PreH20)
       (conj PreH18 PreH17) (conj PreH16 PreH15)
       (conj PreH14 PreH13) (conj PreH12 PreH11))
    as Hinj.
  assert (Heq : u256_of_limbs x0 x1 x2 x3 =
                u256_of_limbs x0_2 x1_2 x2_2 x3_2) by lia.
  specialize (Hinj Heq).
  destruct Hinj as (H0 & H1 & H2 & H3).
  subst x0; subst x1; subst x2; subst x3.
  apply PreH9.
  rewrite !Z.lor_eq_0_iff, !Z.lxor_eq_0_iff.
  repeat split; reflexivity.
Qed.

Lemma proof_of_montg_equal_one_return_wit_2_split_goal_spatial : montg_equal_one_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_montg_one, store_u256_limbs.
  Exists x0 x1 x2 x3.
  split_pure_spatial.
  - cancel (((&( "MONTG_ONE" )) + (0 * sizeof(UINT64))) # UInt64 |-> x0).
    cancel (((&( "MONTG_ONE" )) + (1 * sizeof(UINT64))) # UInt64 |-> x1).
    cancel (((&( "MONTG_ONE" )) + (2 * sizeof(UINT64))) # UInt64 |-> x2).
    cancel (((&( "MONTG_ONE" )) + (3 * sizeof(UINT64))) # UInt64 |-> x3).
  - dump_pre_spatial.
    lia.
Qed.

Lemma proof_of_montg_equal_one_return_wit_2 : montg_equal_one_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_montg_equal_one_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_montg_equal_one_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_montg_equal_one_which_implies_wit_1 : montg_equal_one_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_montg_equal_one_derive_field_by_raw : montg_equal_one_derive_field_by_raw.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod, store_u256.
  rewrite !u32_v_field_address_eq.
  Intros.
  subst P_field.
  Exists A_field.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    entailer!.
    repeat apply derivable1_orp_elim.
    + Intros retval.
      Right.
      Exists retval; entailer!.
    + Intros retval.
      Left.
      Exists retval; entailer!.
Qed. 
