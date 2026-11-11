From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import affine_to_jacobian_goal affine_to_jacobian_proof_auto affine_to_jacobian_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include ecc_point_copy_steps_strategy_proof.
  Include affine_to_jacobian_proof_auto.
  Include affine_to_jacobian_proof_manual.
End VC_Correctness.
