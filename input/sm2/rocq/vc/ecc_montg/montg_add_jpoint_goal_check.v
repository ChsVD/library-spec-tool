From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_add_jpoint_goal montg_add_jpoint_proof_auto montg_add_jpoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include montg_add_jpoint_precompute_strategy_proof.
  Include montg_add_jpoint_x_strategy_proof.
  Include montg_add_jpoint_y_strategy_proof.
  Include montg_add_jpoint_z_strategy_proof.
  Include sm2_representation_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_point_overwrite_strategy_proof.
  Include ecc_point_facts_strategy_proof.
  Include montg_add_jpoint_compare_strategy_proof.
  Include montg_add_jpoint_cleanup_strategy_proof.
  Include montg_add_jpoint_result_strategy_proof.
  Include montg_add_jpoint_proof_auto.
  Include montg_add_jpoint_proof_manual.
End VC_Correctness.
