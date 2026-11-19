From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_one_sided_policy_opt_goal build_one_sided_policy_opt_proof_auto build_one_sided_policy_opt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include fme_gmp_strategy_proof.
  Include safeexec_fme_gmp_strategy_proof.
  Include build_one_sided_policy_opt_proof_auto.
  Include build_one_sided_policy_opt_proof_manual.
End VC_Correctness.
