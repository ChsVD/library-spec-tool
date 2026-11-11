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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_keypair_def.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_keypair_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_keypair_proof_auto.
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

Lemma proof_of_sm2_keypair_entail_wit_3_split_goal_1 : sm2_keypair_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_keypair_entail_wit_3_split_goal_2 : sm2_keypair_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_keypair_entail_wit_3_split_goal_3 : sm2_keypair_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_keypair_entail_wit_3_split_goal_4 : sm2_keypair_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_sm2_keypair_entail_wit_3 : sm2_keypair_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sm2_keypair_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_sm2_keypair_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_sm2_keypair_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_sm2_keypair_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_sm2_keypair_return_wit_1_split_goal_spatial : sm2_keypair_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_keypair_return_wit_1 : sm2_keypair_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists D_2.
  unfold store_sm2_keypair_globals.
  entailer!.
Qed.

Lemma proof_of_sm2_keypair_partial_solve_wit_2_pure_split_goal_1 : sm2_keypair_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_keypair_partial_solve_wit_2_pure_split_goal_2 : sm2_keypair_partial_solve_wit_2_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_keypair_partial_solve_wit_2_pure : sm2_keypair_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  change (0 <= u64_list_value (1 :: 0 :: 0 :: 0 :: nil)).
  rewrite u64_list_value_four.
  unfold u256_of_limbs.
  lia.
Qed.

Lemma proof_of_sm2_keypair_partial_solve_wit_10_pure_split_goal_1 : sm2_keypair_partial_solve_wit_10_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_keypair_partial_solve_wit_10_pure : sm2_keypair_partial_solve_wit_10_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  apply (valid_sm2_private_key_from_rejection_checks D DPlus).
  - lia.
  - exact PreH10.
  - exact PreH15.
  - exact PreH5.
Qed.
