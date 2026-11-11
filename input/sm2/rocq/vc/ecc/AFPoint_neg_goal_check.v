From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import AFPoint_neg_goal AFPoint_neg_proof_auto AFPoint_neg_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_point_copy_steps_strategy_proof.
  Include AFPoint_neg_proof_auto.
  Include AFPoint_neg_proof_manual.
End VC_Correctness.
