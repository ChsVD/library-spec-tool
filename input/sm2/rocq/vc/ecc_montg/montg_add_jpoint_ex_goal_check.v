From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_add_jpoint_ex_goal montg_add_jpoint_ex_proof_auto montg_add_jpoint_ex_proof_manual.

Module VC_Correctness : VC_Correct.
  Include montg_add_jpoint_ex_proof_auto.
  Include montg_add_jpoint_ex_proof_manual.
End VC_Correctness.
