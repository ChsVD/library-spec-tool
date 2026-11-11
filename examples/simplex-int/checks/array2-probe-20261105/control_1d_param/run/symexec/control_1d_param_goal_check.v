From Array2Probe Require Import control_1d_param_goal control_1d_param_proof_auto control_1d_param_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include control_1d_param_proof_auto.
  Include control_1d_param_proof_manual.
End VC_Correctness.
