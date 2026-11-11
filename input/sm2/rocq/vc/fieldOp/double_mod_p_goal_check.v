From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import double_mod_p_goal double_mod_p_proof_auto double_mod_p_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include double_mod_p_proof_auto.
  Include double_mod_p_proof_manual.
End VC_Correctness.
