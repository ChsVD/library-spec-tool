From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import bignum_is_equal_goal bignum_is_equal_proof_auto bignum_is_equal_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include bignum_is_equal_proof_auto.
  Include bignum_is_equal_proof_manual.
End VC_Correctness.
