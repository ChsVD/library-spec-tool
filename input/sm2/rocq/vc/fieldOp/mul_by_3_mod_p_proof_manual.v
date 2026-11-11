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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_by_3_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_by_3_mod_p_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.

Lemma proof_of_mul_by_3_mod_p_return_wit_1_in_place_split_goal_1 : mul_by_3_mod_p_return_wit_1_in_place_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite u64_list_value_four.
  assert (Hvalue_mod : A_in_place mod SM2_P_Z = A_in_place).
  { apply Z.mod_small. lia. }
  assert (Hmul3 :
    ((2 * A_in_place) mod SM2_P_Z + A_in_place) mod SM2_P_Z =
    (3 * A_in_place) mod SM2_P_Z).
  {
    replace A_in_place with (A_in_place mod SM2_P_Z) at 2
      by exact Hvalue_mod.
    rewrite <- Z.add_mod by lia.
    f_equal.
    ring.
  }
  rewrite <- PreH1.
  exact Hmul3.
Qed.

Lemma proof_of_mul_by_3_mod_p_return_wit_1_in_place : mul_by_3_mod_p_return_wit_1_in_place.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mul_by_3_mod_p_return_wit_1_in_place_split_goal_1.
Qed.

Lemma proof_of_mul_by_3_mod_p_return_wit_2_non_alias_split_goal_1 : mul_by_3_mod_p_return_wit_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite u64_list_value_four.
  assert (Hvalue_mod : A_non_alias mod SM2_P_Z = A_non_alias).
  { apply Z.mod_small. lia. }
  assert (Hmul3 :
    ((2 * A_non_alias) mod SM2_P_Z + A_non_alias) mod SM2_P_Z =
    (3 * A_non_alias) mod SM2_P_Z).
  {
    replace A_non_alias with (A_non_alias mod SM2_P_Z) at 2
      by exact Hvalue_mod.
    rewrite <- Z.add_mod by lia.
    f_equal.
    ring.
  }
  rewrite <- PreH1.
  exact Hmul3.
Qed.

Lemma proof_of_mul_by_3_mod_p_return_wit_2_non_alias_split_goal_2 : mul_by_3_mod_p_return_wit_2_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  symmetry.
  exact PreH1.
Qed.

Lemma proof_of_mul_by_3_mod_p_return_wit_2_non_alias : mul_by_3_mod_p_return_wit_2_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_by_3_mod_p_return_wit_2_non_alias_split_goal_1.
  - Goal_apply proof_of_mul_by_3_mod_p_return_wit_2_non_alias_split_goal_2.
Qed.

Lemma proof_of_mul_by_3_mod_p_partial_solve_wit_3_in_place_pure_split_goal_1 : mul_by_3_mod_p_partial_solve_wit_3_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_mul_by_3_mod_p_partial_solve_wit_3_in_place_pure_split_goal_2 : mul_by_3_mod_p_partial_solve_wit_3_in_place_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_mul_by_3_mod_p_partial_solve_wit_3_in_place_pure : mul_by_3_mod_p_partial_solve_wit_3_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  rewrite <- PreH1.
  entailer!.
Qed.

Lemma proof_of_mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1 : mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2 : mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure : mul_by_3_mod_p_partial_solve_wit_4_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  rewrite <- PreH1.
  entailer!.
Qed.

Lemma proof_of_mul_by_3_mod_p_derive_mont_in_place_by_in_place : mul_by_3_mod_p_derive_mont_in_place_by_in_place.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename A_mont_in_place into A.
  Exists (mont_p A).
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    rewrite ec_math_refinement.mont_p_triple.
    entailer!.
Qed.
