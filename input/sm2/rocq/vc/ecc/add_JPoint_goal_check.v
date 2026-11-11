From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_goal add_JPoint_proof_auto add_JPoint_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array_bridges_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include ecc_point_facts_strategy_proof.
  Include ecc_point_copy_steps_strategy_proof.
  Include add_JPoint_boundary_strategy_proof.
  Include add_JPoint_trace_strategy_proof.
  Include add_JPoint_proof_auto.
  Include add_JPoint_proof_manual.
End VC_Correctness.
