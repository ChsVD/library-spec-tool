From SimpleC.EE.Applications_human.simplex_deduction Require Import simplex_deduction_goal simplex_deduction_proof_auto simplex_deduction_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_deduction_proof_auto.
  Include simplex_deduction_proof_manual.
End VC_Correctness.
