From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_apoint_to_montg_goal montg_apoint_to_montg_proof_auto montg_apoint_to_montg_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include montg_apoint_to_montg_proof_auto.
  Include montg_apoint_to_montg_proof_manual.
End VC_Correctness.
