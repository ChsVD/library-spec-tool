From SimpleC.EE.Applications_human.simplex_solve Require Import simplex_solve_goal simplex_solve_proof_auto simplex_solve_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_solve_proof_auto.
  Include simplex_solve_proof_manual.
End VC_Correctness.
