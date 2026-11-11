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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_verify_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_verify_proof_auto.
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

Lemma proof_of_sm2_verify_return_wit_1_split_goal_1 : sm2_verify_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_return_wit_1_split_goal_spatial : sm2_verify_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_return_wit_1 : sm2_verify_return_wit_1.
Proof.
  unfold sm2_verify_return_wit_1.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_message_digest in *.
  unfold store_sm2_verify_dgst_globals.
  entailer!.
Qed.

Lemma proof_of_sm2_verify_return_wit_2_split_goal_1 : sm2_verify_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_return_wit_2_split_goal_spatial : sm2_verify_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_return_wit_2 : sm2_verify_return_wit_2.
Proof.
  unfold sm2_verify_return_wit_2.
  right.
  intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold sm2_message_digest in *.
  unfold store_sm2_verify_dgst_globals.
  entailer!.
Qed.

Lemma proof_of_sm2_verify_partial_solve_wit_3_pure_split_goal_1 : sm2_verify_partial_solve_wit_3_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_partial_solve_wit_3_pure : sm2_verify_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  unfold sm2_id_digest_output_aligned.
  right.
  exact PreH2.
Qed.

Lemma proof_of_sm2_verify_derive_generated_by_verifies : sm2_verify_derive_generated_by_verifies.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_sm2_public_key.
  Intros.
  Exists Message_generated ID_generated P_generated
    SigR_generated SigS_generated.
  apply sepcon_cancel_end.
  - entailer!.
    apply valid_sm2_public_key_noninfinity.
    exact H1.
  - apply derivable1_wand_sepcon_adjoint.
    LLM_pre_process ltac:(lia || nia || int_auto).
    apply derivable1_orp_elim.
    + Intros retval.
      pose proof
        (proj1
          (sm2_signature_verifies_generated_iff
            (be_u8_list_value
              (sm2_message_digest
                ID_generated P_generated Message_generated))
            P_generated SigR_generated SigS_generated H1)
          H5) as Hgenerated.
      destruct Hgenerated as [private_key [Hkeypair Hsignature]].
      Left.
      Exists private_key retval.
      unfold store_sm2_public_key.
      entailer!.
    + Intros retval.
      assert (Hnot_generated :
        ~ (exists private_key,
            valid_sm2_keypair private_key P_generated /\
            sm2_signature_generated
              (be_u8_list_value
                (sm2_message_digest
                  ID_generated P_generated Message_generated))
              private_key SigR_generated SigS_generated)).
      {
        intros Hgenerated.
        apply H5.
        apply
          (proj2
            (sm2_signature_verifies_generated_iff
              (be_u8_list_value
                (sm2_message_digest
                  ID_generated P_generated Message_generated))
              P_generated SigR_generated SigS_generated H1)).
        exact Hgenerated.
      }
      Right.
      Exists retval.
      unfold store_sm2_public_key.
      entailer!.
Qed.
