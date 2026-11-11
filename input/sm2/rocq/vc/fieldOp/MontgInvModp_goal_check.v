From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import MontgInvModp_goal MontgInvModp_proof_auto MontgInvModp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include MontgInvModp_proof_auto.
  Include MontgInvModp_proof_manual.
End VC_Correctness.
