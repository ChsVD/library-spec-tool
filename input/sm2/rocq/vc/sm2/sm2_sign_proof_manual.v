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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_sign_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_sign_proof_auto.
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

Lemma proof_of_sm2_sign_return_wit_1_split_goal_1 : sm2_sign_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_sign_return_wit_1_split_goal_spatial : sm2_sign_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_sign_return_wit_1 : sm2_sign_return_wit_1.
Proof.
  unfold sm2_sign_return_wit_1.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_message_digest in *.
  unfold store_sm2_sign_dgst_globals.
  entailer!.
Qed.

Lemma proof_of_sm2_sign_partial_solve_wit_4_pure_split_goal_1 : sm2_sign_partial_solve_wit_4_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_sign_partial_solve_wit_4_pure : sm2_sign_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  unfold sm2_id_digest_output_aligned.
  right.
  exact PreH10.
Qed.

Lemma proof_of_sm2_sign_derive_verifies_by_generated : sm2_sign_derive_verifies_by_generated.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists Message_verifies ID_verifies D_verifies P_verifies.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros R S retval.
    pose proof
      (sm2_generated_signature_verifies _ _ _ _ _ H1 H3) as Hverify.
    Exists R S retval.
    entailer!.
Qed.
