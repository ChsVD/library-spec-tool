From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_equal_one_goal montg_equal_one_proof_auto montg_equal_one_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include montg_equal_one_proof_auto.
  Include montg_equal_one_proof_manual.
End VC_Correctness.
