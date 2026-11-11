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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_get_id_digest_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_get_id_digest_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope sac.

Lemma proof_of_sm2_get_id_digest_entail_wit_12_split_goal_1 : sm2_get_id_digest_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_entail_wit_12 : sm2_get_id_digest_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_entla_bytes.
  unfold unsigned_last_nbits, SM2_BYTE_BASE.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  repeat rewrite Z.mod_mod by lia.
  replace (id_len_pre * 8) with (8 * id_len_pre) by ring.
  entailer!.
  repeat rewrite Z.rem_eq by lia.
  replace
    (8 * id_len_pre / 256 -
       256 * (8 * id_len_pre / 256 ÷ 256))
    with
    (8 * id_len_pre / 256 +
       (-(8 * id_len_pre / 256 ÷ 256)) * 256) by ring.
  rewrite Z.mod_add by lia.
  replace
    (8 * id_len_pre - 256 * (8 * id_len_pre ÷ 256))
    with
    (8 * id_len_pre + (-(8 * id_len_pre ÷ 256)) * 256) by ring.
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.

Lemma proof_of_sm2_get_id_digest_entail_wit_21_split_goal_1 : sm2_get_id_digest_entail_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof sm2_p_montgomery_bounds as [[Hp0 Hp256] _].
  assert (HA : rev bytes_5 = u256_to_be_bytes SM2_A_Z).
  {
    apply u256_to_be_bytes_from_little_endian; try assumption.
    unfold U256_MOD in Hp256. lia.
  }
  assert (HB : rev bytes_6 = u256_to_be_bytes SM2_B_Z).
  {
    apply u256_to_be_bytes_from_little_endian; try assumption.
    unfold U256_MOD in Hp256. lia.
  }
  assert (HX : rev bytes_3 = u256_to_be_bytes x).
  {
    apply u256_to_be_bytes_from_little_endian; try assumption.
    unfold U256_MOD in Hp256. lia.
  }
  assert (HY : rev bytes_4 = u256_to_be_bytes y).
  {
    apply u256_to_be_bytes_from_little_endian; try assumption.
    unfold U256_MOD in Hp256. lia.
  }
  assert (HPX : rev bytes = u256_to_be_bytes x_2).
  {
    apply u256_to_be_bytes_from_little_endian; try assumption.
    unfold U256_MOD in Hp256. lia.
  }
  assert (HPY : rev bytes_2 = u256_to_be_bytes y_2).
  {
    apply u256_to_be_bytes_from_little_endian; try assumption.
    unfold U256_MOD in Hp256. lia.
  }
  rewrite HA, HB, HX, HY, HPX, HPY.
  reflexivity.
Qed.

Lemma proof_of_sm2_get_id_digest_entail_wit_21 : sm2_get_id_digest_entail_wit_21.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sm2_get_id_digest_entail_wit_21_split_goal_1.
Qed.

Lemma proof_of_sm2_get_id_digest_entail_wit_26_split_goal_1 : sm2_get_id_digest_entail_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite sm2_za_input_length, PreH36.
  lia.
Qed.

Lemma proof_of_sm2_get_id_digest_entail_wit_26_split_goal_2 : sm2_get_id_digest_entail_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply sm2_za_input_bounded.
  exact PreH37.
Qed.

Lemma proof_of_sm2_get_id_digest_entail_wit_26_split_goal_3 : sm2_get_id_digest_entail_wit_26_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_za_input.
  change (sm2_point_x SM2_G_POINT) with SM2_G_X_Z in PreH64.
  change (sm2_point_y SM2_G_POINT) with SM2_G_Y_Z in PreH63.
  rewrite PreH64, PreH63, PreH66, PreH65.
  rewrite PreH36.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_sm2_get_id_digest_entail_wit_26 : sm2_get_id_digest_entail_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm2_get_id_digest_entail_wit_26_split_goal_1.
  - Goal_apply proof_of_sm2_get_id_digest_entail_wit_26_split_goal_2.
  - Goal_apply proof_of_sm2_get_id_digest_entail_wit_26_split_goal_3.
Qed.

Lemma proof_of_sm2_get_id_digest_return_wit_1_split_goal_1 : sm2_get_id_digest_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_return_wit_1_split_goal_spatial : sm2_get_id_digest_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_return_wit_1 : sm2_get_id_digest_return_wit_1.
Proof.
  unfold sm2_get_id_digest_return_wit_1.
  right; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_za_digest, store_sm2_a, store_sm2_b, store_fp, store_mod.
  entailer!.
Qed.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_1 : sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_2 : sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_3 : sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_4 : sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_5 : sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_6 : sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_17_pure : sm2_get_id_digest_partial_solve_wit_17_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst x; subst y; subst x_2; subst y_2; subst retval.
  entailer!.
  - pose proof (Zlength_nonneg ID). lia.
  - unfold u8_list_bounded.
    rewrite !limb_list_bounded_app.
    repeat match goal with | |- _ /\ _ => split end.
    all: apply u256_to_be_bytes_bounded; lia.
  - unfold u8_list_bounded.
    rewrite !limb_list_bounded_app.
    repeat match goal with | |- _ /\ _ => split end.
    all: apply u256_to_be_bytes_bounded.
    all: try lia.
Qed.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_18_pure_split_goal_1 : sm2_get_id_digest_partial_solve_wit_18_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_18_pure_split_goal_2 : sm2_get_id_digest_partial_solve_wit_18_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_get_id_digest_partial_solve_wit_18_pure : sm2_get_id_digest_partial_solve_wit_18_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  - unfold sm3_digest_input_aligned.
    right. exact PreH69.
  - eapply sm2_id_digest_output_aligned_success; eauto.
Qed.
