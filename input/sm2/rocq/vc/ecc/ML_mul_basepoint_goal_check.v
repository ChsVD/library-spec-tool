From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import ML_mul_basepoint_goal ML_mul_basepoint_proof_auto ML_mul_basepoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include basepoint_bytes_strategy_proof.
  Include basepoint_table_points_strategy_proof.
  Include ML_mul_basepoint_proof_auto.
  Include ML_mul_basepoint_proof_manual.
End VC_Correctness.
