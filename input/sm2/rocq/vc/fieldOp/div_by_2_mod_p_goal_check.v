From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import div_by_2_mod_p_goal div_by_2_mod_p_proof_auto div_by_2_mod_p_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include u32_alias_strategy_proof.
  Include div_by_2_mod_p_proof_auto.
  Include div_by_2_mod_p_proof_manual.
End VC_Correctness.
