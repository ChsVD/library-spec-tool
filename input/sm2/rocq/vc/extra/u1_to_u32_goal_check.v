From SimpleC.EE.Applications_human.sm2.vc.extra Require Import u1_to_u32_goal u1_to_u32_proof_auto u1_to_u32_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include byte_memory_views_strategy_proof.
  Include u1_to_u32_proof_auto.
  Include u1_to_u32_proof_manual.
End VC_Correctness.
