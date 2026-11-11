From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_jpoint_to_apoint_goal montg_jpoint_to_apoint_proof_auto montg_jpoint_to_apoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include u32_alias_strategy_proof.
  Include ecc_montg_helper_views_strategy_proof.
  Include montg_jpoint_to_apoint_proof_auto.
  Include montg_jpoint_to_apoint_proof_manual.
End VC_Correctness.
