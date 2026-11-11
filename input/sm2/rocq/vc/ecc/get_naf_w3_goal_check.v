From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import get_naf_w3_goal get_naf_w3_proof_auto get_naf_w3_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include get_naf_w3_proof_auto.
  Include get_naf_w3_proof_manual.
End VC_Correctness.
