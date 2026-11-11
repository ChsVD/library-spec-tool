From SimpleC.EE.Applications_human.sm2.vc.extra Require Import str_reverse_in_place_goal str_reverse_in_place_proof_auto str_reverse_in_place_proof_manual.

Module VC_Correctness : VC_Correct.
  Include byte_memory_views_strategy_proof.
  Include byte_pointer_views_strategy_proof.
  Include str_reverse_in_place_proof_auto.
  Include str_reverse_in_place_proof_manual.
End VC_Correctness.
