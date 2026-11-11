From SimpleC.EE.Applications_human.simplex_checked_add Require Import simplex_checked_add_goal simplex_checked_add_proof_auto simplex_checked_add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_checked_add_proof_auto.
  Include simplex_checked_add_proof_manual.
End VC_Correctness.
