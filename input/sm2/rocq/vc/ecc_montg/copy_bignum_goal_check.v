From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import copy_bignum_goal copy_bignum_proof_auto copy_bignum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sm2_representation_strategy_proof.
  Include copy_bignum_proof_auto.
  Include copy_bignum_proof_manual.
End VC_Correctness.
