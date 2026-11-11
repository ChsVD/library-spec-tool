From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_get_id_digest_goal sm2_get_id_digest_proof_auto sm2_get_id_digest_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include byte_memory_views_strategy_proof.
  Include sm2_protocol_views_strategy_proof.
  Include sm2_za_buffers_strategy_proof.
  Include sm2_get_id_digest_proof_auto.
  Include sm2_get_id_digest_proof_manual.
End VC_Correctness.
