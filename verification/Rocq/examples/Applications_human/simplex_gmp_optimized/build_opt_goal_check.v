From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_opt_goal build_opt_proof_auto build_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include fme_gmp_strategy_proof.
  Include safeexec_fme_gmp_strategy_proof.
  Include build_opt_proof_auto.
  Include build_opt_proof_manual.
End VC_Correctness.
