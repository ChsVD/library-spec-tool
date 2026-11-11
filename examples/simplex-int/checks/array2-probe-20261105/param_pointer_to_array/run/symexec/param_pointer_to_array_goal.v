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
forall (M: (@list (@list Z))) (a_pre: Z),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray2.full a_pre 2 3 M )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition probe_safety_wit_2 :=
forall (M: (@list (@list Z))) (a_pre: Z),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray2.full a_pre 2 3 M )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition probe_safety_wit_3 :=
forall (M: (@list (@list Z))) (a_pre: Z),
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray2.full a_pre 2 3 M )
|--
  “ (7 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 7) ”
.

Definition probe_safety_wit_4 :=
forall (M: (@list (@list Z))) (a_pre: Z) __default__List_Z,
  (IntArray2.full a_pre 2 3 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition probe_safety_wit_5 :=
forall (M: (@list (@list Z))) (a_pre: Z) __default__List_Z,
  (IntArray2.full a_pre 2 3 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition probe_return_wit_1 :=
(
forall (M: (@list (@list Z))) (a_pre: Z) __default__List_Z,
  (IntArray2.full a_pre 2 3 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) )
|--
  EX (N: (@list (@list Z))),
  “ ((Znth (2) ((Znth 1 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) __default__List_Z)) (0)) = 7) ”
  &&  (IntArray2.full a_pre 2 3 N )
) \/
(
forall (M: (@list (@list Z))) __default__List_Z,
  TT && emp 
|--
  “ ((Znth (2) ((Znth 1 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) __default__List_Z)) (0)) = 7) ”
  &&  emp
).

Definition probe_return_wit_1_split_goal_1 :=
forall (M: (@list (@list Z))) __default__List_Z,
  ((Znth (2) ((Znth 1 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) __default__List_Z)) (0)) = 7)
.

Definition probe_partial_solve_wit_1 :=
forall (M: (@list (@list Z))) (a_pre: Z) __default__List_Z,
  (IntArray2.full a_pre 2 3 M )
|--
  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i (a_pre + (1 * (3 * sizeof(INT)))) 2 0 3 (Znth 1 M __default__List_Z) )
  **  (IntArray2.missing_i a_pre 1 0 2 3 M )
.

Definition probe_partial_solve_wit_2 :=
forall (M: (@list (@list Z))) (a_pre: Z) __default__List_Z,
  (IntArray2.full a_pre 2 3 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) )
|--
  ((((a_pre + (1 * (3 * sizeof(INT)))) + (2 * sizeof(INT)))) # Int  |-> (Znth (2) ((Znth 1 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) __default__List_Z)) (0)))
  **  (IntArray.missing_i (a_pre + (1 * (3 * sizeof(INT)))) 2 0 3 (Znth 1 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) __default__List_Z) )
  **  (IntArray2.missing_i a_pre 1 0 2 3 (replace_Znth (1) ((replace_Znth (2) (7) ((Znth 1 M __default__List_Z)))) (M)) )
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
Axiom proof_of_probe_partial_solve_wit_2 : probe_partial_solve_wit_2.

End VC_Correct.
