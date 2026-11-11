From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import double_JPoint_goal double_JPoint_proof_auto double_JPoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_point_copy_steps_strategy_proof.
  Include jpoint_double_trace_strategy_proof.
  Include double_JPoint_proof_auto.
  Include double_JPoint_proof_manual.
End VC_Correctness.
