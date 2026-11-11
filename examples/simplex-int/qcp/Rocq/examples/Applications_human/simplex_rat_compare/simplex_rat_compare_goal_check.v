From SimpleC.EE.Applications_human.simplex_rat_compare Require Import simplex_rat_compare_goal simplex_rat_compare_proof_auto simplex_rat_compare_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_rat_compare_proof_auto.
  Include simplex_rat_compare_proof_manual.
End VC_Correctness.
