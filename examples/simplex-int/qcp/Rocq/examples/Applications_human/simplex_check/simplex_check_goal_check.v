From SimpleC.EE.Applications_human.simplex_check Require Import simplex_check_goal simplex_check_proof_auto simplex_check_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_check_proof_auto.
  Include simplex_check_proof_manual.
End VC_Correctness.
