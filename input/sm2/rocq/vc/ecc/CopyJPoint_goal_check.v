From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import CopyJPoint_goal CopyJPoint_proof_auto CopyJPoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include CopyJPoint_proof_auto.
  Include CopyJPoint_proof_manual.
End VC_Correctness.
