From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import is_on_curve_goal is_on_curve_proof_auto is_on_curve_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include ecc_representation_strategy_proof.
  Include ecc_constants_strategy_proof.
  Include is_on_curve_proof_auto.
  Include is_on_curve_proof_manual.
End VC_Correctness.
