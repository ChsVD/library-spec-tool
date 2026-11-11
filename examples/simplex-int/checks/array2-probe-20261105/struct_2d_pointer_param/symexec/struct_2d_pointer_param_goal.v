From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Local Open Scope sac.
From SimpleC.Verification Require Import array2_strategy_goal.
From SimpleC.Verification Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function probe -----*)

Definition probe_safety_wit_1 :=
forall (p_pre: Z),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition probe_safety_wit_2 :=
forall (p_pre: Z),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |->_)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition probe_safety_wit_3 :=
forall (p_pre: Z),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |->_)
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition probe_safety_wit_4 :=
forall (p_pre: Z),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition probe_safety_wit_5 :=
forall (p_pre: Z),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition probe_return_wit_1 :=
forall (p_pre: Z),
  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
|--
  “ (7 = 7) ”
  &&  ((((&((p_pre)  # "Matrix" ->ₛ "a") + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_probe_safety_wit_1 : probe_safety_wit_1.
Axiom proof_of_probe_safety_wit_2 : probe_safety_wit_2.
Axiom proof_of_probe_safety_wit_3 : probe_safety_wit_3.
Axiom proof_of_probe_safety_wit_4 : probe_safety_wit_4.
Axiom proof_of_probe_safety_wit_5 : probe_safety_wit_5.
Axiom proof_of_probe_return_wit_1 : probe_return_wit_1.

End VC_Correct.
