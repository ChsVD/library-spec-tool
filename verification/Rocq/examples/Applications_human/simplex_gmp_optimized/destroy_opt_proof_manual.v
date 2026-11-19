From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import destroy_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import destroy_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.destroy_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Local Open Scope sac.

Lemma proof_of_destroy_entail_wit_1_split_goal_1 : destroy_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_2 : destroy_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_3 : destroy_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_4 : destroy_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_5 : destroy_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_6 : destroy_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_7 : destroy_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_8 : destroy_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_9 : destroy_entail_wit_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1_split_goal_10 : destroy_entail_wit_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  lazymatch goal with
  | Hdim : simplex_dimensions_ok ?m ?n,
    Hlayout : _ -> simplex_mpz_layout |- _ =>
      pose proof (simplex_destroy_release_bounds m n Hdim Hlayout) as Hbounds
  end.
  tauto.
Qed.

Lemma proof_of_destroy_entail_wit_1 : destroy_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_8.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_9.
  - Goal_apply proof_of_destroy_entail_wit_1_split_goal_10.
Qed.

