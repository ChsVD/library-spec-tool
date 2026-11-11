From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_times_point_naf_w3_goal montg_times_point_naf_w3_proof_auto montg_times_point_naf_w3_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_point_copy_steps_strategy_proof.
  Include ecc_point_overwrite_strategy_proof.
  Include wnaf3_precomp_points_strategy_proof.
  Include wnaf3_predicate_cancellation_strategy_proof.
  Include montg_times_point_naf_w3_proof_auto.
  Include montg_times_point_naf_w3_proof_manual.
End VC_Correctness.
