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
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Local Open Scope sac.

(*----- Function checked_mul -----*)

Definition checked_mul_safety_wit_1_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = A_out_undef)) (PreH2 : (y_pre = B_out_undef)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_mul_safety_wit_2_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = A_out_known)) (PreH2 : (y_pre = B_out_known)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_mul_safety_wit_3_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = A_out_undef)) (PreH2 : (y_pre = B_out_undef)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_4_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = A_out_known)) (PreH2 : (y_pre = B_out_known)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_5_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = A_out_known)) (PreH2 : (y_pre = B_out_known)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_6_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = A_out_undef)) (PreH2 : (y_pre = B_out_undef)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_7_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = A_out_known)) (PreH2 : (y_pre = B_out_known)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_8_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = A_out_undef)) (PreH2 : (y_pre = B_out_undef)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_9_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_mul_safety_wit_10_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_mul_safety_wit_11_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_12_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_13_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_14_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_15_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_16_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_17_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_18_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_19_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_known)) (PreH4 : (y_pre = B_out_known)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_20_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_undef)) (PreH4 : (y_pre = B_out_undef)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_21_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_known)) (PreH4 : (y_pre = B_out_known)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_22_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_undef)) (PreH4 : (y_pre = B_out_undef)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_23_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A_out_known)) (PreH5 : (y_pre = B_out_known)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_24_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A_out_undef)) (PreH5 : (y_pre = B_out_undef)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_25_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A_out_known)) (PreH5 : (y_pre = B_out_known)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_26_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A_out_undef)) (PreH5 : (y_pre = B_out_undef)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_27_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A_out_known)) (PreH5 : (y_pre = B_out_known)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_28_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A_out_undef)) (PreH5 : (y_pre = B_out_undef)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_29_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_known)) (PreH6 : (y_pre = B_out_known)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_30_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_undef)) (PreH6 : (y_pre = B_out_undef)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_31_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_known)) (PreH6 : (y_pre = B_out_known)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_32_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_undef)) (PreH6 : (y_pre = B_out_undef)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_33_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_known)) (PreH6 : (y_pre = B_out_known)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_34_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_undef)) (PreH6 : (y_pre = B_out_undef)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_35_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_known)) (PreH6 : (y_pre = B_out_known)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_36_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_undef)) (PreH6 : (y_pre = B_out_undef)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_37_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_known)) (PreH6 : (y_pre = B_out_known)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_38_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_undef)) (PreH6 : (y_pre = B_out_undef)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_39_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_known)) (PreH6 : (y_pre = B_out_known)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_40_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A_out_undef)) (PreH6 : (y_pre = B_out_undef)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_41_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ False ”
.

Definition checked_mul_safety_wit_42_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ False ”
.

Definition checked_mul_safety_wit_43_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ False ”
.

Definition checked_mul_safety_wit_44_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ False ”
.

Definition checked_mul_safety_wit_45_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ ((-y_pre) <> (-1))) ” 
  &&  “ ((-y_pre) <> 0) ”
.

Definition checked_mul_safety_wit_46_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ ((-y_pre) <> (-1))) ” 
  &&  “ ((-y_pre) <> 0) ”
.

Definition checked_mul_safety_wit_47_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ ((-y_pre) <> (-1))) ” 
  &&  “ ((-y_pre) <> 0) ”
.

Definition checked_mul_safety_wit_48_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ ((-y_pre) <> (-1))) ” 
  &&  “ ((-y_pre) <> 0) ”
.

Definition checked_mul_safety_wit_49_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition checked_mul_safety_wit_50_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition checked_mul_safety_wit_51_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition checked_mul_safety_wit_52_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition checked_mul_safety_wit_53_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_54_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_55_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_56_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_57_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_58_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_59_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_60_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_61_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_62_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_63_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_64_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_65_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_66_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_67_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_68_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_69_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_70_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_71_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_72_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_73_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_73_out_known_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_73_out_known_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_74_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_74_out_undef_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_74_out_undef_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_75_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_75_out_known_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_75_out_known_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_76_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_76_out_undef_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_76_out_undef_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_77_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_77_out_known_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_77_out_known_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_78_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_78_out_undef_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_78_out_undef_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_79_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_79_out_known_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_79_out_known_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old_out_known)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_80_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_80_out_undef_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_80_out_undef_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_81_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_82_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_83_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_84_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_85_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_86_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_87_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_88_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_89_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_90_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_91_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_92_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_return_wit_1_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_undef * B_out_undef ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_1_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_2_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_known * B_out_known ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_2_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_3_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_undef * B_out_undef ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_3_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_undef)) (PreH7 : (y_pre = B_out_undef)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_4_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_known * B_out_known ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_4_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A_out_known)) (PreH7 : (y_pre = B_out_known)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_5_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_known * B_out_known ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_5_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_6_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_undef * B_out_undef ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_6_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_7_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_known * B_out_known ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_7_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_8_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_undef * B_out_undef ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_8_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_9_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_known * B_out_known ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_9_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_10_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_undef * B_out_undef ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_10_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_11_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_known * B_out_known ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_11_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_12_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A_out_undef * B_out_undef ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_12_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_13_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |-> old_out_known)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_13_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_14_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_14_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_15_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |-> old_out_known)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_15_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_16_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_16_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_17_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |-> old_out_known)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_17_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_18_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_18_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_19_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |-> old_out_known)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_19_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_known)) (PreH8 : (y_pre = B_out_known)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_20_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_20_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A_out_undef)) (PreH8 : (y_pre = B_out_undef)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_21_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_21_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_undef)) (PreH3 : (y_pre = B_out_undef)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_22_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |-> old_out_known)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_22_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A_out_known)) (PreH3 : (y_pre = B_out_known)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_23_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_known)) (PreH4 : (y_pre = B_out_known)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |-> old_out_known)
|--
  “ (0 = (checked_mul_flag (A_out_known) (B_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |-> old_out_known)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_known)) (PreH4 : (y_pre = B_out_known)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_23_out_known_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_known)) (PreH4 : (y_pre = B_out_known)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_24_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_undef)) (PreH4 : (y_pre = B_out_undef)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A_out_undef) (B_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_undef)) (PreH4 : (y_pre = B_out_undef)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_24_out_undef_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A_out_undef)) (PreH4 : (y_pre = B_out_undef)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Module Type VC_Correct.


Axiom proof_of_checked_mul_safety_wit_1_out_undef : checked_mul_safety_wit_1_out_undef.
Axiom proof_of_checked_mul_safety_wit_2_out_known : checked_mul_safety_wit_2_out_known.
Axiom proof_of_checked_mul_safety_wit_3_out_undef : checked_mul_safety_wit_3_out_undef.
Axiom proof_of_checked_mul_safety_wit_4_out_known : checked_mul_safety_wit_4_out_known.
Axiom proof_of_checked_mul_safety_wit_5_out_known : checked_mul_safety_wit_5_out_known.
Axiom proof_of_checked_mul_safety_wit_6_out_undef : checked_mul_safety_wit_6_out_undef.
Axiom proof_of_checked_mul_safety_wit_7_out_known : checked_mul_safety_wit_7_out_known.
Axiom proof_of_checked_mul_safety_wit_8_out_undef : checked_mul_safety_wit_8_out_undef.
Axiom proof_of_checked_mul_safety_wit_9_out_known : checked_mul_safety_wit_9_out_known.
Axiom proof_of_checked_mul_safety_wit_10_out_undef : checked_mul_safety_wit_10_out_undef.
Axiom proof_of_checked_mul_safety_wit_11_out_known : checked_mul_safety_wit_11_out_known.
Axiom proof_of_checked_mul_safety_wit_12_out_undef : checked_mul_safety_wit_12_out_undef.
Axiom proof_of_checked_mul_safety_wit_13_out_undef : checked_mul_safety_wit_13_out_undef.
Axiom proof_of_checked_mul_safety_wit_14_out_known : checked_mul_safety_wit_14_out_known.
Axiom proof_of_checked_mul_safety_wit_15_out_undef : checked_mul_safety_wit_15_out_undef.
Axiom proof_of_checked_mul_safety_wit_16_out_known : checked_mul_safety_wit_16_out_known.
Axiom proof_of_checked_mul_safety_wit_17_out_undef : checked_mul_safety_wit_17_out_undef.
Axiom proof_of_checked_mul_safety_wit_18_out_known : checked_mul_safety_wit_18_out_known.
Axiom proof_of_checked_mul_safety_wit_19_out_known : checked_mul_safety_wit_19_out_known.
Axiom proof_of_checked_mul_safety_wit_20_out_undef : checked_mul_safety_wit_20_out_undef.
Axiom proof_of_checked_mul_safety_wit_21_out_known : checked_mul_safety_wit_21_out_known.
Axiom proof_of_checked_mul_safety_wit_22_out_undef : checked_mul_safety_wit_22_out_undef.
Axiom proof_of_checked_mul_safety_wit_23_out_known : checked_mul_safety_wit_23_out_known.
Axiom proof_of_checked_mul_safety_wit_24_out_undef : checked_mul_safety_wit_24_out_undef.
Axiom proof_of_checked_mul_safety_wit_25_out_known : checked_mul_safety_wit_25_out_known.
Axiom proof_of_checked_mul_safety_wit_26_out_undef : checked_mul_safety_wit_26_out_undef.
Axiom proof_of_checked_mul_safety_wit_27_out_known : checked_mul_safety_wit_27_out_known.
Axiom proof_of_checked_mul_safety_wit_28_out_undef : checked_mul_safety_wit_28_out_undef.
Axiom proof_of_checked_mul_safety_wit_29_out_known : checked_mul_safety_wit_29_out_known.
Axiom proof_of_checked_mul_safety_wit_30_out_undef : checked_mul_safety_wit_30_out_undef.
Axiom proof_of_checked_mul_safety_wit_31_out_known : checked_mul_safety_wit_31_out_known.
Axiom proof_of_checked_mul_safety_wit_32_out_undef : checked_mul_safety_wit_32_out_undef.
Axiom proof_of_checked_mul_safety_wit_33_out_known : checked_mul_safety_wit_33_out_known.
Axiom proof_of_checked_mul_safety_wit_34_out_undef : checked_mul_safety_wit_34_out_undef.
Axiom proof_of_checked_mul_safety_wit_35_out_known : checked_mul_safety_wit_35_out_known.
Axiom proof_of_checked_mul_safety_wit_36_out_undef : checked_mul_safety_wit_36_out_undef.
Axiom proof_of_checked_mul_safety_wit_37_out_known : checked_mul_safety_wit_37_out_known.
Axiom proof_of_checked_mul_safety_wit_38_out_undef : checked_mul_safety_wit_38_out_undef.
Axiom proof_of_checked_mul_safety_wit_39_out_known : checked_mul_safety_wit_39_out_known.
Axiom proof_of_checked_mul_safety_wit_40_out_undef : checked_mul_safety_wit_40_out_undef.
Axiom proof_of_checked_mul_safety_wit_41_out_known : checked_mul_safety_wit_41_out_known.
Axiom proof_of_checked_mul_safety_wit_42_out_undef : checked_mul_safety_wit_42_out_undef.
Axiom proof_of_checked_mul_safety_wit_43_out_known : checked_mul_safety_wit_43_out_known.
Axiom proof_of_checked_mul_safety_wit_44_out_undef : checked_mul_safety_wit_44_out_undef.
Axiom proof_of_checked_mul_safety_wit_45_out_known : checked_mul_safety_wit_45_out_known.
Axiom proof_of_checked_mul_safety_wit_46_out_undef : checked_mul_safety_wit_46_out_undef.
Axiom proof_of_checked_mul_safety_wit_47_out_known : checked_mul_safety_wit_47_out_known.
Axiom proof_of_checked_mul_safety_wit_48_out_undef : checked_mul_safety_wit_48_out_undef.
Axiom proof_of_checked_mul_safety_wit_49_out_known : checked_mul_safety_wit_49_out_known.
Axiom proof_of_checked_mul_safety_wit_50_out_undef : checked_mul_safety_wit_50_out_undef.
Axiom proof_of_checked_mul_safety_wit_51_out_known : checked_mul_safety_wit_51_out_known.
Axiom proof_of_checked_mul_safety_wit_52_out_undef : checked_mul_safety_wit_52_out_undef.
Axiom proof_of_checked_mul_safety_wit_53_out_undef : checked_mul_safety_wit_53_out_undef.
Axiom proof_of_checked_mul_safety_wit_54_out_known : checked_mul_safety_wit_54_out_known.
Axiom proof_of_checked_mul_safety_wit_55_out_undef : checked_mul_safety_wit_55_out_undef.
Axiom proof_of_checked_mul_safety_wit_56_out_known : checked_mul_safety_wit_56_out_known.
Axiom proof_of_checked_mul_safety_wit_57_out_undef : checked_mul_safety_wit_57_out_undef.
Axiom proof_of_checked_mul_safety_wit_58_out_known : checked_mul_safety_wit_58_out_known.
Axiom proof_of_checked_mul_safety_wit_59_out_undef : checked_mul_safety_wit_59_out_undef.
Axiom proof_of_checked_mul_safety_wit_60_out_known : checked_mul_safety_wit_60_out_known.
Axiom proof_of_checked_mul_safety_wit_61_out_known : checked_mul_safety_wit_61_out_known.
Axiom proof_of_checked_mul_safety_wit_62_out_undef : checked_mul_safety_wit_62_out_undef.
Axiom proof_of_checked_mul_safety_wit_63_out_known : checked_mul_safety_wit_63_out_known.
Axiom proof_of_checked_mul_safety_wit_64_out_undef : checked_mul_safety_wit_64_out_undef.
Axiom proof_of_checked_mul_safety_wit_65_out_known : checked_mul_safety_wit_65_out_known.
Axiom proof_of_checked_mul_safety_wit_66_out_undef : checked_mul_safety_wit_66_out_undef.
Axiom proof_of_checked_mul_safety_wit_67_out_known : checked_mul_safety_wit_67_out_known.
Axiom proof_of_checked_mul_safety_wit_68_out_undef : checked_mul_safety_wit_68_out_undef.
Axiom proof_of_checked_mul_safety_wit_69_out_undef : checked_mul_safety_wit_69_out_undef.
Axiom proof_of_checked_mul_safety_wit_70_out_known : checked_mul_safety_wit_70_out_known.
Axiom proof_of_checked_mul_safety_wit_71_out_undef : checked_mul_safety_wit_71_out_undef.
Axiom proof_of_checked_mul_safety_wit_72_out_known : checked_mul_safety_wit_72_out_known.
Axiom proof_of_checked_mul_safety_wit_73_out_known : checked_mul_safety_wit_73_out_known.
Axiom proof_of_checked_mul_safety_wit_74_out_undef : checked_mul_safety_wit_74_out_undef.
Axiom proof_of_checked_mul_safety_wit_75_out_known : checked_mul_safety_wit_75_out_known.
Axiom proof_of_checked_mul_safety_wit_76_out_undef : checked_mul_safety_wit_76_out_undef.
Axiom proof_of_checked_mul_safety_wit_77_out_known : checked_mul_safety_wit_77_out_known.
Axiom proof_of_checked_mul_safety_wit_78_out_undef : checked_mul_safety_wit_78_out_undef.
Axiom proof_of_checked_mul_safety_wit_79_out_known : checked_mul_safety_wit_79_out_known.
Axiom proof_of_checked_mul_safety_wit_80_out_undef : checked_mul_safety_wit_80_out_undef.
Axiom proof_of_checked_mul_safety_wit_81_out_undef : checked_mul_safety_wit_81_out_undef.
Axiom proof_of_checked_mul_safety_wit_82_out_known : checked_mul_safety_wit_82_out_known.
Axiom proof_of_checked_mul_safety_wit_83_out_undef : checked_mul_safety_wit_83_out_undef.
Axiom proof_of_checked_mul_safety_wit_84_out_known : checked_mul_safety_wit_84_out_known.
Axiom proof_of_checked_mul_safety_wit_85_out_known : checked_mul_safety_wit_85_out_known.
Axiom proof_of_checked_mul_safety_wit_86_out_undef : checked_mul_safety_wit_86_out_undef.
Axiom proof_of_checked_mul_safety_wit_87_out_known : checked_mul_safety_wit_87_out_known.
Axiom proof_of_checked_mul_safety_wit_88_out_undef : checked_mul_safety_wit_88_out_undef.
Axiom proof_of_checked_mul_safety_wit_89_out_known : checked_mul_safety_wit_89_out_known.
Axiom proof_of_checked_mul_safety_wit_90_out_undef : checked_mul_safety_wit_90_out_undef.
Axiom proof_of_checked_mul_safety_wit_91_out_known : checked_mul_safety_wit_91_out_known.
Axiom proof_of_checked_mul_safety_wit_92_out_undef : checked_mul_safety_wit_92_out_undef.
Axiom proof_of_checked_mul_return_wit_1_out_undef : checked_mul_return_wit_1_out_undef.
Axiom proof_of_checked_mul_return_wit_2_out_known : checked_mul_return_wit_2_out_known.
Axiom proof_of_checked_mul_return_wit_3_out_undef : checked_mul_return_wit_3_out_undef.
Axiom proof_of_checked_mul_return_wit_4_out_known : checked_mul_return_wit_4_out_known.
Axiom proof_of_checked_mul_return_wit_5_out_known : checked_mul_return_wit_5_out_known.
Axiom proof_of_checked_mul_return_wit_6_out_undef : checked_mul_return_wit_6_out_undef.
Axiom proof_of_checked_mul_return_wit_7_out_known : checked_mul_return_wit_7_out_known.
Axiom proof_of_checked_mul_return_wit_8_out_undef : checked_mul_return_wit_8_out_undef.
Axiom proof_of_checked_mul_return_wit_9_out_known : checked_mul_return_wit_9_out_known.
Axiom proof_of_checked_mul_return_wit_10_out_undef : checked_mul_return_wit_10_out_undef.
Axiom proof_of_checked_mul_return_wit_11_out_known : checked_mul_return_wit_11_out_known.
Axiom proof_of_checked_mul_return_wit_12_out_undef : checked_mul_return_wit_12_out_undef.
Axiom proof_of_checked_mul_return_wit_13_out_known : checked_mul_return_wit_13_out_known.
Axiom proof_of_checked_mul_return_wit_14_out_undef : checked_mul_return_wit_14_out_undef.
Axiom proof_of_checked_mul_return_wit_15_out_known : checked_mul_return_wit_15_out_known.
Axiom proof_of_checked_mul_return_wit_16_out_undef : checked_mul_return_wit_16_out_undef.
Axiom proof_of_checked_mul_return_wit_17_out_known : checked_mul_return_wit_17_out_known.
Axiom proof_of_checked_mul_return_wit_18_out_undef : checked_mul_return_wit_18_out_undef.
Axiom proof_of_checked_mul_return_wit_19_out_known : checked_mul_return_wit_19_out_known.
Axiom proof_of_checked_mul_return_wit_20_out_undef : checked_mul_return_wit_20_out_undef.
Axiom proof_of_checked_mul_return_wit_21_out_undef : checked_mul_return_wit_21_out_undef.
Axiom proof_of_checked_mul_return_wit_22_out_known : checked_mul_return_wit_22_out_known.
Axiom proof_of_checked_mul_return_wit_23_out_known : checked_mul_return_wit_23_out_known.
Axiom proof_of_checked_mul_return_wit_24_out_undef : checked_mul_return_wit_24_out_undef.

End VC_Correct.
