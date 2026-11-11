From Array2Probe Require Import global_2d_goal global_2d_proof_auto global_2d_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include global_2d_proof_auto.
  Include global_2d_proof_manual.
End VC_Correctness.
