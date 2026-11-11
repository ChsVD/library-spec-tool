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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_add_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_add_proof_auto.
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

Lemma proof_of_u32_add_return_wit_1_r_eq_b_split_goal_1 : u32_add_return_wit_1_r_eq_b_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_1_r_eq_b_split_goal_2 : u32_add_return_wit_1_r_eq_b_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_1_r_eq_b_split_goal_3 : u32_add_return_wit_1_r_eq_b_split_goal_3.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_1_r_eq_b : u32_add_return_wit_1_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsum :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
      u256_of_limbs x0 x1 x2 x3 =
    u256_of_limbs out out_2 out_3 out_4 + retval * U256_MOD).
  {
    apply (u256_add_carry_chain
      x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3
      out out_2 out_3 out_4 retval_2 retval_3 retval_4 retval);
      lia.
  }
  assert (Hrange :
    0 <= u256_of_limbs out out_2 out_3 out_4 < U256_MOD).
  {
    apply u256_of_limbs_range; lia.
  }
  Exists (u256_of_limbs out out_2 out_3 out_4).
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

Lemma proof_of_u32_add_return_wit_2_r_eq_a_split_goal_1 : u32_add_return_wit_2_r_eq_a_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_2_r_eq_a_split_goal_2 : u32_add_return_wit_2_r_eq_a_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_2_r_eq_a_split_goal_3 : u32_add_return_wit_2_r_eq_a_split_goal_3.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_2_r_eq_a : u32_add_return_wit_2_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsum :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
      u256_of_limbs x0 x1 x2 x3 =
    u256_of_limbs out out_2 out_3 out_4 + retval * U256_MOD).
  {
    apply (u256_add_carry_chain
      x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3
      out out_2 out_3 out_4 retval_2 retval_3 retval_4 retval);
      lia.
  }
  assert (Hrange :
    0 <= u256_of_limbs out out_2 out_3 out_4 < U256_MOD).
  {
    apply u256_of_limbs_range; lia.
  }
  Exists (u256_of_limbs out out_2 out_3 out_4).
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

Lemma proof_of_u32_add_return_wit_3_non_alias_split_goal_1 : u32_add_return_wit_3_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_3_non_alias_split_goal_2 : u32_add_return_wit_3_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_3_non_alias_split_goal_3 : u32_add_return_wit_3_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_u32_add_return_wit_3_non_alias : u32_add_return_wit_3_non_alias.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsum :
    u256_of_limbs x0_2 x1_2 x2_2 x3_2 +
      u256_of_limbs x0 x1 x2 x3 =
    u256_of_limbs out out_2 out_3 out_4 + retval * U256_MOD).
  {
    apply (u256_add_carry_chain
      x0_2 x1_2 x2_2 x3_2 x0 x1 x2 x3
      out out_2 out_3 out_4 retval_2 retval_3 retval_4 retval);
      lia.
  }
  assert (Hrange :
    0 <= u256_of_limbs out out_2 out_3 out_4 < U256_MOD).
  {
    apply u256_of_limbs_range; lia.
  }
  Exists (u256_of_limbs out out_2 out_3 out_4).
  unfold store_u256, store_u256_limbs.
  rewrite UInt64Array.undef_seg_empty.
  Exists x0_2 x1_2 x2_2 x3_2.
  Exists x0 x1 x2 x3.
  Exists out out_2 out_3 out_4.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    try assumption;
    lia.
Qed. 
