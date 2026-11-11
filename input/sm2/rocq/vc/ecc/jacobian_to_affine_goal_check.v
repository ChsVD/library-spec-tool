From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import jacobian_to_affine_goal jacobian_to_affine_proof_auto jacobian_to_affine_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include jacobian_to_affine_proof_auto.
  Include jacobian_to_affine_proof_manual.
End VC_Correctness.
