From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import montg_sqr_mod_p_goal montg_sqr_mod_p_proof_auto montg_sqr_mod_p_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include montg_sqr_mod_p_proof_auto.
  Include montg_sqr_mod_p_proof_manual.
End VC_Correctness.
