From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2n_mong_mul_core_goal sm2n_mong_mul_core_proof_auto sm2n_mong_mul_core_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include sm2n_mong_mul_core_proof_auto.
  Include sm2n_mong_mul_core_proof_manual.
End VC_Correctness.
