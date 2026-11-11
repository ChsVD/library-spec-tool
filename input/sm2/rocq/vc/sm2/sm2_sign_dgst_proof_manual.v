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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_sign_dgst_def.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_sign_dgst_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_sign_dgst_proof_auto.
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

Lemma proof_of_sm2_sign_dgst_entail_wit_2_split_goal_1 : sm2_sign_dgst_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_2_split_goal_2 : sm2_sign_dgst_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_2_split_goal_3 : sm2_sign_dgst_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (0 <= 0).
  lia.
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_2_split_goal_4 : sm2_sign_dgst_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_2_split_goal_5 : sm2_sign_dgst_entail_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (0 <= 0).
  lia.
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_2 : sm2_sign_dgst_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm2_sign_dgst_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_sm2_sign_dgst_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_sm2_sign_dgst_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_sm2_sign_dgst_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_sm2_sign_dgst_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_11_1_split_goal_1 : sm2_sign_dgst_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_signature_generated.
  split.
  - exact PreH8.
  - exists K, RX, RY, Ainv.
    repeat split.
    all: try assumption; try lia.
    + cbv [u256_of_limbs U64_MOD] in PreH7.
      rewrite Zmult_mod.
      rewrite (Z.mod_small Ainv SM2_N_Z) by lia.
      replace (1 + D) with (D + 1) by ring.
      exact PreH7.
    + symmetry.
      apply Z.add_mod.
      pose proof sm2_n_bounds; lia.
    + rewrite Zmult_mod_idemp_r.
      set (RR :=
        Zmod
          (Zmod (be_u8_list_value DigestBytes) SM2_N_Z +
           Zmod RX SM2_N_Z)
          SM2_N_Z) in *.
      replace ((K - RR * D) * Ainv)
        with (Ainv * (K - RR * D)) by ring.
      rewrite
        (Zmult_mod Ainv
          (K - Zmod (RR * D) SM2_N_Z) SM2_N_Z).
      rewrite (Zmult_mod Ainv (K - RR * D) SM2_N_Z).
      rewrite Zminus_mod_idemp_r.
      reflexivity.
Qed.

Lemma proof_of_sm2_sign_dgst_entail_wit_11_1 : sm2_sign_dgst_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sm2_sign_dgst_entail_wit_11_1_split_goal_1.
Qed.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_7_pure_split_goal_1 : sm2_sign_dgst_partial_solve_wit_7_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_7_pure : sm2_sign_dgst_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  rewrite (named_afpoint_u32_v_addr_eq "rand_AFPoint" "x").
  rewrite nested_afpoint_u32_v_addr_eq.
  rewrite u32_v_field_address_eq.
  rewrite afpoint_x_field_address_eq.
  rewrite Z.mul_0_l, Z.add_0_r.
  apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_8_pure_split_goal_1 : sm2_sign_dgst_partial_solve_wit_8_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_8_pure : sm2_sign_dgst_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (store_u256_undef_neq
      (&( &( "rand_AFPoint" ) ->ₛ "x"))
      (&( "tmp")) RX) as Hneq.
  unfold UndefStructPredu32 in Hneq.
  rewrite u32_v_field_address_eq in Hneq.
  rewrite (global_u32_v_addr_eq "tmp"), u32_v_field_address_eq.
  sep_apply Hneq.
  entailer!.
Qed.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_1 : sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_2 : sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_3 : sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_4 : sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_5 : sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_6 : sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_6.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_18_pure : sm2_sign_dgst_partial_solve_wit_18_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_19_pure_split_goal_1 : sm2_sign_dgst_partial_solve_wit_19_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_sign_dgst_partial_solve_wit_19_pure : sm2_sign_dgst_partial_solve_wit_19_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold valid_sm2_private_key in PreH2.
  cbv [u256_of_limbs U64_MOD].
  rewrite Z.mod_small by (pose proof sm2_n_bounds; lia).
  entailer!.
Qed.
