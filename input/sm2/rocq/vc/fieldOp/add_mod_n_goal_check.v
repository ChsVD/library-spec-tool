From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_n_goal add_mod_n_proof_auto add_mod_n_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include sm2_constants_strategy_proof.
  Include add_mod_n_proof_auto.
  Include add_mod_n_proof_manual.
End VC_Correctness.
