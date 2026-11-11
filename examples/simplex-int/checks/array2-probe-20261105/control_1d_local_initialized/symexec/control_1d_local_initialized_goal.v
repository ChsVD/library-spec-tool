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
  (IntArray.full ( &( "a" ) ) 6 (repeat_Z (0) (6)) )
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition probe_safety_wit_2 :=
  (IntArray.full ( &( "a" ) ) 6 (repeat_Z (0) (6)) )
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition probe_safety_wit_3 :=
  (IntArray.full ( &( "a" ) ) 6 (replace_Znth (5) (7) ((repeat_Z (0) (6)))) )
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition probe_return_wit_1 :=
  TT && emp 
|--
  “ (7 = 7) ”
  &&  emp
.

Definition probe_partial_solve_wit_1 :=
  (IntArray.full ( &( "a" ) ) 6 (repeat_Z (0) (6)) )
|--
  (((( &( "a" ) ) + (5 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "a" ) ) 5 0 6 (repeat_Z (0) (6)) )
.

Definition probe_partial_solve_wit_2 :=
  (IntArray.full ( &( "a" ) ) 6 (replace_Znth (5) (7) ((repeat_Z (0) (6)))) )
|--
  (((( &( "a" ) ) + (5 * sizeof(INT)))) # Int  |-> 7)
  **  (IntArray.missing_i ( &( "a" ) ) 5 0 6 (replace_Znth (5) (7) ((repeat_Z (0) (6)))) )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_probe_safety_wit_1 : probe_safety_wit_1.
Axiom proof_of_probe_safety_wit_2 : probe_safety_wit_2.
Axiom proof_of_probe_safety_wit_3 : probe_safety_wit_3.
Axiom proof_of_probe_return_wit_1 : probe_return_wit_1.
Axiom proof_of_probe_partial_solve_wit_1 : probe_partial_solve_wit_1.
Axiom proof_of_probe_partial_solve_wit_2 : probe_partial_solve_wit_2.

End VC_Correct.
