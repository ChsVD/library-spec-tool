From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import sm2p_mong_mul_goal sm2p_mong_mul_proof_auto sm2p_mong_mul_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include sm2p_mong_mul_proof_auto.
  Include sm2p_mong_mul_proof_manual.
End VC_Correctness.
