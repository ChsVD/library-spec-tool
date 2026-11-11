From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_eq_one_goal u32_eq_one_proof_auto u32_eq_one_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include u32_eq_one_proof_auto.
  Include u32_eq_one_proof_manual.
End VC_Correctness.
