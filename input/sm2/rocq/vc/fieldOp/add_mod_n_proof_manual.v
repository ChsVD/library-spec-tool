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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_n_def.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_n_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_n_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.

Lemma proof_of_add_mod_n_entail_wit_6_1_non_alias : add_mod_n_entail_wit_6_1_non_alias.
Proof.
  unfold add_mod_n_entail_wit_6_1_non_alias.
  right; intros.
  assert (Hadd : A_non_alias + B_non_alias =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_N_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_n_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_n_no_reduction_arithmetic
    A_non_alias B_non_alias
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_n_tmp (A_non_alias + B_non_alias)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_n_entail_wit_6_2_non_alias : add_mod_n_entail_wit_6_2_non_alias.
Proof.
  unfold add_mod_n_entail_wit_6_2_non_alias.
  right; intros.
  assert (Hadd : A_non_alias + B_non_alias =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_N_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_n_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_n_reduction_arithmetic
    A_non_alias B_non_alias
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_n_tmp (A_non_alias + B_non_alias)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_n_entail_wit_7_1_r_eq_b : add_mod_n_entail_wit_7_1_r_eq_b.
Proof.
  unfold add_mod_n_entail_wit_7_1_r_eq_b.
  right; intros.
  assert (Hadd : A_r_eq_b + B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_N_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_n_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_n_no_reduction_arithmetic
    A_r_eq_b B_r_eq_b
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_n_tmp (A_r_eq_b + B_r_eq_b)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_n_entail_wit_7_2_r_eq_b : add_mod_n_entail_wit_7_2_r_eq_b.
Proof.
  unfold add_mod_n_entail_wit_7_2_r_eq_b.
  right; intros.
  assert (Hadd : A_r_eq_b + B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + retval_4 * U256_MOD).
  {
    rewrite PreH59, PreH50.
    apply (u256_add_carry_chain
      x0 x1 x2 x3 x0_2 x1_2 x2_2 x3_2
      out out_2 out_3 out_4 retval retval_2 retval_3 retval_4); lia.
  }
  assert (Hsub :
    u256_of_limbs out out_2 out_3 out_4 + U256_MOD - SM2_N_Z =
    u256_of_limbs out_5 out_6 out_7 out_8 + retval_8 * U256_MOD).
  {
    apply (add_mod_n_sub_carry_chain
      out out_2 out_3 out_4 out_5 out_6 out_7 out_8
      retval_5 retval_6 retval_7 retval_8); assumption.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HT.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (add_mod_n_reduction_arithmetic
    A_r_eq_b B_r_eq_b
    (u256_of_limbs out out_2 out_3 out_4)
    (u256_of_limbs out_5 out_6 out_7 out_8)
    retval_4 retval_8
    ltac:(lia) ltac:(lia) HT HD ltac:(lia) ltac:(lia)
    Hadd Hsub PreH9) as [Hvalue Htmpmod].
  finish_add_mod_n_tmp (A_r_eq_b + B_r_eq_b)
    out out_2 out_3 out_4 Hvalue Htmpmod.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_1 : add_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_2 : add_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_10_r_eq_b_pure : add_mod_n_partial_solve_wit_10_r_eq_b_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_10_r_eq_b_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N0_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_1 : add_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_2 : add_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_12_non_alias_pure : add_mod_n_partial_solve_wit_12_non_alias_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_12_non_alias_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N0_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_1 : add_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_2 : add_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_14_r_eq_b_pure : add_mod_n_partial_solve_wit_14_r_eq_b_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_14_r_eq_b_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N1_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_1 : add_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_2 : add_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_16_non_alias_pure : add_mod_n_partial_solve_wit_16_non_alias_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_16_non_alias_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N1_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_1 : add_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_2 : add_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_18_r_eq_b_pure : add_mod_n_partial_solve_wit_18_r_eq_b_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_18_r_eq_b_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N2_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_1 : add_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_2 : add_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_20_non_alias_pure : add_mod_n_partial_solve_wit_20_non_alias_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_20_non_alias_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N2_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_1 : add_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_2 : add_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_22_r_eq_b_pure : add_mod_n_partial_solve_wit_22_r_eq_b_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_22_r_eq_b_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N3_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 

Lemma proof_of_add_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_1 : add_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_2 : add_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_add_mod_n_partial_solve_wit_24_non_alias_pure : add_mod_n_partial_solve_wit_24_non_alias_pure.
Proof.
  unfold add_mod_n_partial_solve_wit_24_non_alias_pure.
  right; intros.
  pose proof
    (unsigned_Lastnbits_range (Z.lnot SM2_N3_Z) 64 ltac:(lia))
    as Hrange.
  entailer_with ltac:(assumption || lia).
  unfold U64_MOD.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia]; lia.
Qed. 
