From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import MontgInvModn_goal MontgInvModn_proof_auto MontgInvModn_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include MontgInvModn_proof_auto.
  Include MontgInvModn_proof_manual.
End VC_Correctness.
