From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import inv_for_mul_mod_n_goal inv_for_mul_mod_n_proof_auto inv_for_mul_mod_n_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include inv_for_mul_mod_n_proof_auto.
  Include inv_for_mul_mod_n_proof_manual.
End VC_Correctness.
