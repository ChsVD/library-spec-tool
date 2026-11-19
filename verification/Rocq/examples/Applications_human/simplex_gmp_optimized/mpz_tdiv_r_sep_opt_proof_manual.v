From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import mpz_tdiv_r_sep_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import mpz_tdiv_r_sep_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.mpz_tdiv_r_sep_opt_lib.
Local Open Scope sac.

Lemma proof_of_mpz_tdiv_r_entail_wit_1_split_goal_spatial : mpz_tdiv_r_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  cancel (store_Z r_pre old_separated_trunc).
  cancel (store_Z n_pre zn_separated_trunc).
  apply sepcon_cancel_end.
  - cancel.
  - apply emp_to_optional_store_Z_null. reflexivity.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_tdiv_r_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1_split_goal_spatial : mpz_tdiv_r_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (simplex_tdiv_r_math_rem _ _ _ _ PreH1) as Hrem.
  subst rv.
  cancel (store_Z r_pre (Z.rem zn_separated_trunc zd_separated_trunc)).
  cancel (store_Z n_pre zn_separated_trunc).
  apply sepcon_cancel_lhs_emp.
  unfold optional_store_Z.
  Split.
  - Intros_p Hnull. cancel.
  - Intros_p Hnonnull. exfalso. apply Hnonnull. reflexivity.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_tdiv_r_return_wit_1_split_goal_spatial.
Qed.

