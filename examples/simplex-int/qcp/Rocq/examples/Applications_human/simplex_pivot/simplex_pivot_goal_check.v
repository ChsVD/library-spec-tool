From SimpleC.EE.Applications_human.simplex_pivot Require Import simplex_pivot_goal simplex_pivot_proof_auto simplex_pivot_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_pivot_proof_auto.
  Include simplex_pivot_proof_manual.
End VC_Correctness.
