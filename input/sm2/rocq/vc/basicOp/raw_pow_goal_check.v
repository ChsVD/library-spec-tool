From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import raw_pow_goal raw_pow_proof_auto raw_pow_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include raw_pow_arrays_strategy_proof.
  Include raw_pow_proof_auto.
  Include raw_pow_proof_manual.
End VC_Correctness.
