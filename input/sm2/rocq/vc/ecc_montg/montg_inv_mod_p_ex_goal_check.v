From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_inv_mod_p_ex_goal montg_inv_mod_p_ex_proof_auto montg_inv_mod_p_ex_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_montg_helper_views_strategy_proof.
  Include montg_inv_mod_p_ex_proof_auto.
  Include montg_inv_mod_p_ex_proof_manual.
End VC_Correctness.
