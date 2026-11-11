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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_p_proof_auto.
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

Lemma proof_of_inv_for_mul_mod_p_partial_solve_wit_3_in_place_pure_split_goal_1 : inv_for_mul_mod_p_partial_solve_wit_3_in_place_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_inv_for_mul_mod_p_partial_solve_wit_3_in_place_pure_split_goal_2 : inv_for_mul_mod_p_partial_solve_wit_3_in_place_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_inv_for_mul_mod_p_partial_solve_wit_3_in_place_pure : inv_for_mul_mod_p_partial_solve_wit_3_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mont_p_range Ainv_in).
  entailer!.
Qed. 

Lemma proof_of_inv_for_mul_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1 : inv_for_mul_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_inv_for_mul_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2 : inv_for_mul_mod_p_partial_solve_wit_4_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_inv_for_mul_mod_p_partial_solve_wit_4_non_alias_pure : inv_for_mul_mod_p_partial_solve_wit_4_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (mont_p_range Ainv_non).
  entailer!.
Qed. 

