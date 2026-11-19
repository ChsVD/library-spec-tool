From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import mpz_tdiv_r_sep_opt_goal mpz_tdiv_r_sep_opt_proof_auto mpz_tdiv_r_sep_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_tdiv_r_sep_opt_proof_auto.
  Include mpz_tdiv_r_sep_opt_proof_manual.
End VC_Correctness.
