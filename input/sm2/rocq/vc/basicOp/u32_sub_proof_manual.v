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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_sub_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_sub_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_u32_sub_return_wit_1_r_eq_b : u32_sub_return_wit_1_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prepare_sub_math x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    PreH20 PreH15 PreH10 PreH5 PreH30 PreH21.
  Exists borrow (u256_of_limbs out out_2 out_3 out_4).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 out out_2 out_3 out_4.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed.

Lemma proof_of_u32_sub_return_wit_2_r_eq_a : u32_sub_return_wit_2_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prepare_sub_math x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    PreH20 PreH15 PreH10 PreH5 PreH30 PreH21.
  Exists borrow (u256_of_limbs out out_2 out_3 out_4).
  unfold store_u256, store_u256_limbs.
  Exists out out_2 out_3 out_4 x0 x1 x2 x3.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed.

Lemma proof_of_u32_sub_return_wit_3_non_alias : u32_sub_return_wit_3_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prepare_sub_math x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    PreH20 PreH15 PreH10 PreH5 PreH30 PreH21.
  Exists borrow (u256_of_limbs out out_2 out_3 out_4).
  unfold store_u256, store_u256_limbs.
  Exists x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3 out out_2 out_3 out_4.
  rewrite UInt64Array.undef_seg_empty.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_1_r_eq_b_pure_split_goal_1 : u32_sub_partial_solve_wit_1_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_1_r_eq_b_pure_split_goal_2 : u32_sub_partial_solve_wit_1_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_1_r_eq_b_pure : u32_sub_partial_solve_wit_1_r_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x0 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_2_r_eq_a_pure_split_goal_1 : u32_sub_partial_solve_wit_2_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_2_r_eq_a_pure_split_goal_2 : u32_sub_partial_solve_wit_2_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_2_r_eq_a_pure : u32_sub_partial_solve_wit_2_r_eq_a_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x0 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_3_non_alias_pure_split_goal_1 : u32_sub_partial_solve_wit_3_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_3_non_alias_pure_split_goal_2 : u32_sub_partial_solve_wit_3_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_3_non_alias_pure : u32_sub_partial_solve_wit_3_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x0 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_4_r_eq_b_pure_split_goal_1 : u32_sub_partial_solve_wit_4_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_4_r_eq_b_pure_split_goal_2 : u32_sub_partial_solve_wit_4_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_4_r_eq_b_pure : u32_sub_partial_solve_wit_4_r_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x1 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_5_r_eq_a_pure_split_goal_1 : u32_sub_partial_solve_wit_5_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_5_r_eq_a_pure_split_goal_2 : u32_sub_partial_solve_wit_5_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_5_r_eq_a_pure : u32_sub_partial_solve_wit_5_r_eq_a_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x1 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_6_non_alias_pure_split_goal_1 : u32_sub_partial_solve_wit_6_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_6_non_alias_pure_split_goal_2 : u32_sub_partial_solve_wit_6_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_6_non_alias_pure : u32_sub_partial_solve_wit_6_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x1 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_7_r_eq_b_pure_split_goal_1 : u32_sub_partial_solve_wit_7_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_7_r_eq_b_pure_split_goal_2 : u32_sub_partial_solve_wit_7_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_7_r_eq_b_pure : u32_sub_partial_solve_wit_7_r_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x2 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1 : u32_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2 : u32_sub_partial_solve_wit_8_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_8_r_eq_a_pure : u32_sub_partial_solve_wit_8_r_eq_a_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x2 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_9_non_alias_pure_split_goal_1 : u32_sub_partial_solve_wit_9_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_9_non_alias_pure_split_goal_2 : u32_sub_partial_solve_wit_9_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_9_non_alias_pure : u32_sub_partial_solve_wit_9_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x2 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_10_r_eq_b_pure_split_goal_1 : u32_sub_partial_solve_wit_10_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_10_r_eq_b_pure_split_goal_2 : u32_sub_partial_solve_wit_10_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_10_r_eq_b_pure : u32_sub_partial_solve_wit_10_r_eq_b_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x3 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_11_r_eq_a_pure_split_goal_1 : u32_sub_partial_solve_wit_11_r_eq_a_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_11_r_eq_a_pure_split_goal_2 : u32_sub_partial_solve_wit_11_r_eq_a_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_11_r_eq_a_pure : u32_sub_partial_solve_wit_11_r_eq_a_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x3 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_u32_sub_partial_solve_wit_12_non_alias_pure_split_goal_1 : u32_sub_partial_solve_wit_12_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_12_non_alias_pure_split_goal_2 : u32_sub_partial_solve_wit_12_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_sub_partial_solve_wit_12_non_alias_pure : u32_sub_partial_solve_wit_12_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (unsigned_lnot_u64_range x3 ltac:(lia)) as Hrange.
  split_pures; dump_pre_spatial; try assumption; lia.
Qed.
