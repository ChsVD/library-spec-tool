From Array2Probe Require Import struct_2d_pointer_param_goal struct_2d_pointer_param_proof_auto struct_2d_pointer_param_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include struct_2d_pointer_param_proof_auto.
  Include struct_2d_pointer_param_proof_manual.
End VC_Correctness.
