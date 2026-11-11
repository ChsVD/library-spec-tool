From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import pow_mod_p_goal pow_mod_p_proof_auto pow_mod_p_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include pow_mod_p_proof_auto.
  Include pow_mod_p_proof_manual.
End VC_Correctness.
