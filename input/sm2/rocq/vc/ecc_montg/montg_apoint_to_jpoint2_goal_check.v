From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_apoint_to_jpoint2_goal montg_apoint_to_jpoint2_proof_auto montg_apoint_to_jpoint2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include u32_alias_strategy_proof.
  Include ecc_montg_helper_views_strategy_proof.
  Include montg_apoint_to_jpoint2_proof_auto.
  Include montg_apoint_to_jpoint2_proof_manual.
End VC_Correctness.
