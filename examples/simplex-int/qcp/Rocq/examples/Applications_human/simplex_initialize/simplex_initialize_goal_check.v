From SimpleC.EE.Applications_human.simplex_initialize Require Import simplex_initialize_goal simplex_initialize_proof_auto simplex_initialize_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_initialize_proof_auto.
  Include simplex_initialize_proof_manual.
End VC_Correctness.
