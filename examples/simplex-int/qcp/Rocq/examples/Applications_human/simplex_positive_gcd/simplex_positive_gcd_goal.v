Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_positive_gcd.simplex_positive_gcd_lib.
Local Open Scope sac.

(*----- Function positive_gcd -----*)

Definition positive_gcd_safety_wit_1 := 
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= INT_MAX)) (PreH3 : (0 <= b)) (PreH4 : (b <= INT_MAX)) (PreH5 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition positive_gcd_safety_wit_2 := 
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b <> 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ ((a <> (INT_MIN)) \/ (b <> (-1))) ” 
  &&  “ (b <> 0) ”
.

Definition positive_gcd_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (B: Z) (A: Z) (PreH1 : (a_pre = A)) (PreH2 : (b_pre = B)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ ((Zgcd (a_pre) (b_pre)) = (Zgcd (A) (B))) ”
  &&  emp
.

Definition positive_gcd_entail_wit_2 := 
(
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b <> 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  TT && emp 
|--
  “ (0 <= b) ” 
  &&  “ (b <= INT_MAX) ” 
  &&  “ (0 <= (a % ( b ) )) ” 
  &&  “ ((a % ( b ) ) <= INT_MAX) ” 
  &&  “ ((Zgcd (b) ((a % ( b ) ))) = (Zgcd (A) (B))) ”
  &&  emp
) \/
(
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b <> 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  TT && emp 
|--
  “ ((Zgcd (b) ((a % ( b ) ))) = (Zgcd (A) (B))) ” 
  &&  “ ((a % ( b ) ) <= INT_MAX) ” 
  &&  “ (0 <= (a % ( b ) )) ”
  &&  emp
).

Definition positive_gcd_entail_wit_2_split_goal_1 := 
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b <> 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  ((Zgcd (b) ((a % ( b ) ))) = (Zgcd (A) (B)))
.

Definition positive_gcd_entail_wit_2_split_goal_2 := 
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b <> 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  ((a % ( b ) ) <= INT_MAX)
.

Definition positive_gcd_entail_wit_2_split_goal_3 := 
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b <> 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  (0 <= (a % ( b ) ))
.

Definition positive_gcd_return_wit_1 := 
(
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b = 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  TT && emp 
|--
  “ (a = (Zgcd (A) (B))) ”
  &&  emp
) \/
(
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b = 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  TT && emp 
|--
  “ (a = (Zgcd (A) (B))) ”
  &&  emp
).

Definition positive_gcd_return_wit_1_split_goal_1 := 
forall (B: Z) (A: Z) (b: Z) (a: Z) (PreH1 : (b = 0)) (PreH2 : (0 <= a)) (PreH3 : (a <= INT_MAX)) (PreH4 : (0 <= b)) (PreH5 : (b <= INT_MAX)) (PreH6 : ((Zgcd (a) (b)) = (Zgcd (A) (B)))) ,
  (a = (Zgcd (A) (B)))
.

Module Type VC_Correct.


Axiom proof_of_positive_gcd_safety_wit_1 : positive_gcd_safety_wit_1.
Axiom proof_of_positive_gcd_safety_wit_2 : positive_gcd_safety_wit_2.
Axiom proof_of_positive_gcd_entail_wit_1 : positive_gcd_entail_wit_1.
Axiom proof_of_positive_gcd_entail_wit_2 : positive_gcd_entail_wit_2.
Axiom proof_of_positive_gcd_return_wit_1 : positive_gcd_return_wit_1.

End VC_Correct.
