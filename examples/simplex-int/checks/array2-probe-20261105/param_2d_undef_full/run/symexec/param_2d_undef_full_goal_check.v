From Array2Probe Require Import param_2d_undef_full_goal param_2d_undef_full_proof_auto param_2d_undef_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include param_2d_undef_full_proof_auto.
  Include param_2d_undef_full_proof_manual.
End VC_Correctness.
