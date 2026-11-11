From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import equ_to_JPoint_one_goal equ_to_JPoint_one_proof_auto equ_to_JPoint_one_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include equ_to_JPoint_one_proof_auto.
  Include equ_to_JPoint_one_proof_manual.
End VC_Correctness.
