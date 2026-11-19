From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import combine_opt_goal combine_opt_proof_auto combine_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include fme_gmp_strategy_proof.
  Include safeexec_fme_gmp_strategy_proof.
  Include combine_opt_proof_auto.
  Include combine_opt_proof_manual.
End VC_Correctness.
