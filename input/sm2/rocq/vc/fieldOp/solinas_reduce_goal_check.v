From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import solinas_reduce_goal solinas_reduce_proof_auto solinas_reduce_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include array_bridges_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include solinas_reduce_proof_auto.
  Include solinas_reduce_proof_manual.
End VC_Correctness.
