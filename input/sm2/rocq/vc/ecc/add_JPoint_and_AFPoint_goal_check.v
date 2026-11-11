From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_and_AFPoint_goal add_JPoint_and_AFPoint_proof_auto add_JPoint_and_AFPoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include ecc_point_copy_steps_strategy_proof.
  Include add_JPoint_and_AFPoint_proof_auto.
  Include add_JPoint_and_AFPoint_proof_manual.
End VC_Correctness.
