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
forall (a_pre: Z),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray2.undef_full a_pre 2 3 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition probe_safety_wit_2 :=
forall (a_pre: Z),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray2.undef_full a_pre 2 3 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition probe_safety_wit_3 :=
forall (a_pre: Z),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray2.undef_full a_pre 2 3 )
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition probe_safety_wit_4 :=
forall (a_pre: Z),
  (IntArray.undef_seg (a_pre + (1 * (3 * sizeof(INT)))) 0 2 )
  **  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
  **  (IntArray2.undef_missing_i a_pre 1 0 2 3 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition probe_safety_wit_5 :=
forall (a_pre: Z),
  (IntArray.undef_seg (a_pre + (1 * (3 * sizeof(INT)))) 0 2 )
  **  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
  **  (IntArray2.undef_missing_i a_pre 1 0 2 3 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition probe_return_wit_1 :=
(
forall (a_pre: Z),
  (IntArray.undef_seg (a_pre + (1 * (3 * sizeof(INT)))) 0 2 )
  **  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
  **  (IntArray2.undef_missing_i a_pre 1 0 2 3 )
|--
  EX (N: (@list (@list (@option Z)))),
  “ (7 = 7) ”
  &&  (IntArray2.mixed_full a_pre 2 3 N )
) \/
(
forall (a_pre: Z) (PreH1 : (7 <= INT_MAX)) (PreH2 : (7 >= INT_MIN)),
  (IntArray.undef_seg (a_pre + (1 * (3 * sizeof(INT)))) 0 2 )
  **  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> 7)
  **  (IntArray2.undef_missing_i a_pre 1 0 2 3 )
|--
  EX (N: (@list (@list (@option Z)))),
  (IntArray2.mixed_full a_pre 2 3 N )
).

Definition probe_partial_solve_wit_1 :=
forall (a_pre: Z),
  (IntArray2.undef_full a_pre 2 3 )
|--
  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i (a_pre + (1 * (3 * sizeof(INT)))) 2 0 3 )
  **  (IntArray2.undef_missing_i a_pre 1 0 2 3 )
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
Axiom proof_of_probe_partial_solve_wit_1 : probe_partial_solve_wit_1.

End VC_Correct.
