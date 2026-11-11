From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import portable_addcarryx_u64_goal portable_addcarryx_u64_proof_auto portable_addcarryx_u64_proof_manual.

Module VC_Correctness : VC_Correct.
  Include portable_addcarryx_u64_proof_auto.
  Include portable_addcarryx_u64_proof_manual.
End VC_Correctness.
