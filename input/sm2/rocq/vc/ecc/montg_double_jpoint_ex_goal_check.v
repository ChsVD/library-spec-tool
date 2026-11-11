From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_double_jpoint_ex_goal montg_double_jpoint_ex_proof_auto montg_double_jpoint_ex_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include montg_double_jpoint_ex_proof_auto.
  Include montg_double_jpoint_ex_proof_manual.
End VC_Correctness.
