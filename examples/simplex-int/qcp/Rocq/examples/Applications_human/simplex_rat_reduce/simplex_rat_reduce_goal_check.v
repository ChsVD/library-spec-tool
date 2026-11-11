From SimpleC.EE.Applications_human.simplex_rat_reduce Require Import simplex_rat_reduce_goal simplex_rat_reduce_proof_auto simplex_rat_reduce_proof_manual.

Module VC_Correctness : VC_Correct.
  Include simplex_rat_reduce_proof_auto.
  Include simplex_rat_reduce_proof_manual.
End VC_Correctness.
