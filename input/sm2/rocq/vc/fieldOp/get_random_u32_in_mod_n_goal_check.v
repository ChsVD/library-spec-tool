From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import get_random_u32_in_mod_n_goal get_random_u32_in_mod_n_proof_auto get_random_u32_in_mod_n_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include get_random_u32_in_mod_n_proof_auto.
  Include get_random_u32_in_mod_n_proof_manual.
End VC_Correctness.
