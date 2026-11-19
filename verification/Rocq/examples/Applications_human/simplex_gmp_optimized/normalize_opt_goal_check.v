From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import normalize_opt_goal normalize_opt_proof_auto normalize_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include fme_gmp_strategy_proof.
  Include safeexec_fme_gmp_strategy_proof.
  Include normalize_opt_proof_auto.
  Include normalize_opt_proof_manual.
End VC_Correctness.
