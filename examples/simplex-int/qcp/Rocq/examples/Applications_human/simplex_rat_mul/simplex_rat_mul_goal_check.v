From SimpleC.EE.Applications_human.simplex_rat_mul Require Import simplex_rat_mul_goal simplex_rat_mul_proof_auto simplex_rat_mul_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_rat_mul_proof_auto.
  Include simplex_rat_mul_proof_manual.
End VC_Correctness.
