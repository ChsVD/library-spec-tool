From SimpleC.EE.Applications_human.sm2.vc.sm3 Require Import sm3_update_goal sm3_update_proof_auto sm3_update_proof_manual.

Module VC_Correctness : VC_Correct.
  Include byte_memory_views_strategy_proof.
  Include sm3_ctx_views_strategy_proof.
  Include sm3_streaming_memory_views_strategy_proof.
  Include sm3_update_proof_auto.
  Include sm3_update_proof_manual.
End VC_Correctness.
