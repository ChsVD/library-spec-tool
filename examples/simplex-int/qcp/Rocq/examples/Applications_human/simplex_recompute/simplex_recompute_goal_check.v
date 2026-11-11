From SimpleC.EE.Applications_human.simplex_recompute Require Import simplex_recompute_goal simplex_recompute_proof_auto simplex_recompute_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_recompute_proof_auto.
  Include simplex_recompute_proof_manual.
End VC_Correctness.
