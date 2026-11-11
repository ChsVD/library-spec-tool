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

Definition checked_mul_safety_wit_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
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

Definition checked_mul_safety_wit_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_mul_safety_wit_3 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_4 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_5 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_6 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
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

Definition checked_mul_safety_wit_7 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_8 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
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

Definition checked_mul_safety_wit_9 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_mul_safety_wit_10 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
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

Definition checked_mul_safety_wit_11 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_12 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_13 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
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

Definition checked_mul_safety_wit_14 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_15 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
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

Definition checked_mul_safety_wit_16 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_mul_safety_wit_17 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
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

Definition checked_mul_safety_wit_18 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_19 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_20 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
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

Definition checked_mul_safety_wit_21 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_22 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
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

Definition checked_mul_safety_wit_23 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_24 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_25 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_26 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 0)) ,
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

Definition checked_mul_safety_wit_27 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_28 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 0)) ,
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

Definition checked_mul_safety_wit_29 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_30 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_31 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_32 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (y_pre <> (INT_MIN)) ”
.

Definition checked_mul_safety_wit_33 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_34 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
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

Definition checked_mul_safety_wit_35 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_36 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
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

Definition checked_mul_safety_wit_37 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_38 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre < 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
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

Definition checked_mul_safety_wit_39 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_40 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre >= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
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

Definition checked_mul_safety_wit_41 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ False ”
.

Definition checked_mul_safety_wit_42 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ False ”
.

Definition checked_mul_safety_wit_43 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ False ”
.

Definition checked_mul_safety_wit_44 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) = 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ False ”
.

Definition checked_mul_safety_wit_45 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ ((-y_pre) <> (-1))) ” 
  &&  “ ((-y_pre) <> 0) ”
.

Definition checked_mul_safety_wit_46 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_47 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ ((-y_pre) <> (-1))) ” 
  &&  “ ((-y_pre) <> 0) ”
.

Definition checked_mul_safety_wit_48 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_49 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition checked_mul_safety_wit_50 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_51 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MAX <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition checked_mul_safety_wit_52 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_53 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_54 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_55 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_56 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_57 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_58 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_59 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_60 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-y_pre) <> 0)) (PreH2 : (y_pre < 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_61 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_62 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_63 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_64 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_65 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_66 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_67 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_mul_safety_wit_68 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_69 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_70 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_71 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_72 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_73 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_73_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_73_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_74 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_74_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_74_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_75 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_75_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_75_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_76 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_76_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_76_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> (-y_pre))
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_77 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_77_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_77_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_78 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_78_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_78_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> (-x_pre))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_79 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * y_pre )) ”
).

Definition checked_mul_safety_wit_79_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_79_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_80 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_80_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre * y_pre ) <= INT_MAX) ”
.

Definition checked_mul_safety_wit_80_split_goal_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((( &( "ay" ) )) # Int  |-> y_pre)
  **  ((( &( "ax" ) )) # Int  |-> x_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (x_pre * y_pre )) ”
.

Definition checked_mul_safety_wit_81 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_82 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
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

Definition checked_mul_safety_wit_83 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
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

Definition checked_mul_safety_wit_84 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
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

Definition checked_mul_safety_wit_85 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
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

Definition checked_mul_safety_wit_86 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_87 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
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

Definition checked_mul_safety_wit_88 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_89 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
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

Definition checked_mul_safety_wit_90 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_safety_wit_91 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
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

Definition checked_mul_safety_wit_92 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
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

Definition checked_mul_return_wit_1 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_2 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre >= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_3 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_4 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_4_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = 0)) (PreH2 : (y_pre >= 0)) (PreH3 : (x_pre < 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_5 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_5_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_6 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_6_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_7 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_7_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_8 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_8_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_9 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_9_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_10 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_10_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_11 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_11_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_12 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre * y_pre ))
|--
  “ (1 = (checked_mul_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A * B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_12_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (1 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_13 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_13_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_14 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_14_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_15 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_15_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_16 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_16_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ (-y_pre) ))) (PreH2 : ((-y_pre) <> 0)) (PreH3 : (y_pre < 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_17 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_17_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_18 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_18_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : ((-x_pre) > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre < 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_19 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_19_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 1)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_20 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_20_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX ÷ y_pre ))) (PreH2 : (y_pre <> 0)) (PreH3 : (y_pre >= 0)) (PreH4 : (x_pre >= 0)) (PreH5 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH7 : (x_pre = A)) (PreH8 : (y_pre = B)) (PreH9 : ((INT_MIN) <= x_pre)) (PreH10 : (x_pre <= INT_MAX)) (PreH11 : ((INT_MIN) <= y_pre)) (PreH12 : (y_pre <= INT_MAX)) (PreH13 : (known = 0)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_21 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_21_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_22 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_22_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_23 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_23_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Definition checked_mul_return_wit_24 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_mul_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_mul_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_mul_return_wit_24_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  (0 = (checked_mul_flag (x_pre) (y_pre)))
.

Module Type VC_Correct.


Axiom proof_of_checked_mul_safety_wit_1 : checked_mul_safety_wit_1.
Axiom proof_of_checked_mul_safety_wit_2 : checked_mul_safety_wit_2.
Axiom proof_of_checked_mul_safety_wit_3 : checked_mul_safety_wit_3.
Axiom proof_of_checked_mul_safety_wit_4 : checked_mul_safety_wit_4.
Axiom proof_of_checked_mul_safety_wit_5 : checked_mul_safety_wit_5.
Axiom proof_of_checked_mul_safety_wit_6 : checked_mul_safety_wit_6.
Axiom proof_of_checked_mul_safety_wit_7 : checked_mul_safety_wit_7.
Axiom proof_of_checked_mul_safety_wit_8 : checked_mul_safety_wit_8.
Axiom proof_of_checked_mul_safety_wit_9 : checked_mul_safety_wit_9.
Axiom proof_of_checked_mul_safety_wit_10 : checked_mul_safety_wit_10.
Axiom proof_of_checked_mul_safety_wit_11 : checked_mul_safety_wit_11.
Axiom proof_of_checked_mul_safety_wit_12 : checked_mul_safety_wit_12.
Axiom proof_of_checked_mul_safety_wit_13 : checked_mul_safety_wit_13.
Axiom proof_of_checked_mul_safety_wit_14 : checked_mul_safety_wit_14.
Axiom proof_of_checked_mul_safety_wit_15 : checked_mul_safety_wit_15.
Axiom proof_of_checked_mul_safety_wit_16 : checked_mul_safety_wit_16.
Axiom proof_of_checked_mul_safety_wit_17 : checked_mul_safety_wit_17.
Axiom proof_of_checked_mul_safety_wit_18 : checked_mul_safety_wit_18.
Axiom proof_of_checked_mul_safety_wit_19 : checked_mul_safety_wit_19.
Axiom proof_of_checked_mul_safety_wit_20 : checked_mul_safety_wit_20.
Axiom proof_of_checked_mul_safety_wit_21 : checked_mul_safety_wit_21.
Axiom proof_of_checked_mul_safety_wit_22 : checked_mul_safety_wit_22.
Axiom proof_of_checked_mul_safety_wit_23 : checked_mul_safety_wit_23.
Axiom proof_of_checked_mul_safety_wit_24 : checked_mul_safety_wit_24.
Axiom proof_of_checked_mul_safety_wit_25 : checked_mul_safety_wit_25.
Axiom proof_of_checked_mul_safety_wit_26 : checked_mul_safety_wit_26.
Axiom proof_of_checked_mul_safety_wit_27 : checked_mul_safety_wit_27.
Axiom proof_of_checked_mul_safety_wit_28 : checked_mul_safety_wit_28.
Axiom proof_of_checked_mul_safety_wit_29 : checked_mul_safety_wit_29.
Axiom proof_of_checked_mul_safety_wit_30 : checked_mul_safety_wit_30.
Axiom proof_of_checked_mul_safety_wit_31 : checked_mul_safety_wit_31.
Axiom proof_of_checked_mul_safety_wit_32 : checked_mul_safety_wit_32.
Axiom proof_of_checked_mul_safety_wit_33 : checked_mul_safety_wit_33.
Axiom proof_of_checked_mul_safety_wit_34 : checked_mul_safety_wit_34.
Axiom proof_of_checked_mul_safety_wit_35 : checked_mul_safety_wit_35.
Axiom proof_of_checked_mul_safety_wit_36 : checked_mul_safety_wit_36.
Axiom proof_of_checked_mul_safety_wit_37 : checked_mul_safety_wit_37.
Axiom proof_of_checked_mul_safety_wit_38 : checked_mul_safety_wit_38.
Axiom proof_of_checked_mul_safety_wit_39 : checked_mul_safety_wit_39.
Axiom proof_of_checked_mul_safety_wit_40 : checked_mul_safety_wit_40.
Axiom proof_of_checked_mul_safety_wit_41 : checked_mul_safety_wit_41.
Axiom proof_of_checked_mul_safety_wit_42 : checked_mul_safety_wit_42.
Axiom proof_of_checked_mul_safety_wit_43 : checked_mul_safety_wit_43.
Axiom proof_of_checked_mul_safety_wit_44 : checked_mul_safety_wit_44.
Axiom proof_of_checked_mul_safety_wit_45 : checked_mul_safety_wit_45.
Axiom proof_of_checked_mul_safety_wit_46 : checked_mul_safety_wit_46.
Axiom proof_of_checked_mul_safety_wit_47 : checked_mul_safety_wit_47.
Axiom proof_of_checked_mul_safety_wit_48 : checked_mul_safety_wit_48.
Axiom proof_of_checked_mul_safety_wit_49 : checked_mul_safety_wit_49.
Axiom proof_of_checked_mul_safety_wit_50 : checked_mul_safety_wit_50.
Axiom proof_of_checked_mul_safety_wit_51 : checked_mul_safety_wit_51.
Axiom proof_of_checked_mul_safety_wit_52 : checked_mul_safety_wit_52.
Axiom proof_of_checked_mul_safety_wit_53 : checked_mul_safety_wit_53.
Axiom proof_of_checked_mul_safety_wit_54 : checked_mul_safety_wit_54.
Axiom proof_of_checked_mul_safety_wit_55 : checked_mul_safety_wit_55.
Axiom proof_of_checked_mul_safety_wit_56 : checked_mul_safety_wit_56.
Axiom proof_of_checked_mul_safety_wit_57 : checked_mul_safety_wit_57.
Axiom proof_of_checked_mul_safety_wit_58 : checked_mul_safety_wit_58.
Axiom proof_of_checked_mul_safety_wit_59 : checked_mul_safety_wit_59.
Axiom proof_of_checked_mul_safety_wit_60 : checked_mul_safety_wit_60.
Axiom proof_of_checked_mul_safety_wit_61 : checked_mul_safety_wit_61.
Axiom proof_of_checked_mul_safety_wit_62 : checked_mul_safety_wit_62.
Axiom proof_of_checked_mul_safety_wit_63 : checked_mul_safety_wit_63.
Axiom proof_of_checked_mul_safety_wit_64 : checked_mul_safety_wit_64.
Axiom proof_of_checked_mul_safety_wit_65 : checked_mul_safety_wit_65.
Axiom proof_of_checked_mul_safety_wit_66 : checked_mul_safety_wit_66.
Axiom proof_of_checked_mul_safety_wit_67 : checked_mul_safety_wit_67.
Axiom proof_of_checked_mul_safety_wit_68 : checked_mul_safety_wit_68.
Axiom proof_of_checked_mul_safety_wit_69 : checked_mul_safety_wit_69.
Axiom proof_of_checked_mul_safety_wit_70 : checked_mul_safety_wit_70.
Axiom proof_of_checked_mul_safety_wit_71 : checked_mul_safety_wit_71.
Axiom proof_of_checked_mul_safety_wit_72 : checked_mul_safety_wit_72.
Axiom proof_of_checked_mul_safety_wit_73 : checked_mul_safety_wit_73.
Axiom proof_of_checked_mul_safety_wit_74 : checked_mul_safety_wit_74.
Axiom proof_of_checked_mul_safety_wit_75 : checked_mul_safety_wit_75.
Axiom proof_of_checked_mul_safety_wit_76 : checked_mul_safety_wit_76.
Axiom proof_of_checked_mul_safety_wit_77 : checked_mul_safety_wit_77.
Axiom proof_of_checked_mul_safety_wit_78 : checked_mul_safety_wit_78.
Axiom proof_of_checked_mul_safety_wit_79 : checked_mul_safety_wit_79.
Axiom proof_of_checked_mul_safety_wit_80 : checked_mul_safety_wit_80.
Axiom proof_of_checked_mul_safety_wit_81 : checked_mul_safety_wit_81.
Axiom proof_of_checked_mul_safety_wit_82 : checked_mul_safety_wit_82.
Axiom proof_of_checked_mul_safety_wit_83 : checked_mul_safety_wit_83.
Axiom proof_of_checked_mul_safety_wit_84 : checked_mul_safety_wit_84.
Axiom proof_of_checked_mul_safety_wit_85 : checked_mul_safety_wit_85.
Axiom proof_of_checked_mul_safety_wit_86 : checked_mul_safety_wit_86.
Axiom proof_of_checked_mul_safety_wit_87 : checked_mul_safety_wit_87.
Axiom proof_of_checked_mul_safety_wit_88 : checked_mul_safety_wit_88.
Axiom proof_of_checked_mul_safety_wit_89 : checked_mul_safety_wit_89.
Axiom proof_of_checked_mul_safety_wit_90 : checked_mul_safety_wit_90.
Axiom proof_of_checked_mul_safety_wit_91 : checked_mul_safety_wit_91.
Axiom proof_of_checked_mul_safety_wit_92 : checked_mul_safety_wit_92.
Axiom proof_of_checked_mul_return_wit_1 : checked_mul_return_wit_1.
Axiom proof_of_checked_mul_return_wit_2 : checked_mul_return_wit_2.
Axiom proof_of_checked_mul_return_wit_3 : checked_mul_return_wit_3.
Axiom proof_of_checked_mul_return_wit_4 : checked_mul_return_wit_4.
Axiom proof_of_checked_mul_return_wit_5 : checked_mul_return_wit_5.
Axiom proof_of_checked_mul_return_wit_6 : checked_mul_return_wit_6.
Axiom proof_of_checked_mul_return_wit_7 : checked_mul_return_wit_7.
Axiom proof_of_checked_mul_return_wit_8 : checked_mul_return_wit_8.
Axiom proof_of_checked_mul_return_wit_9 : checked_mul_return_wit_9.
Axiom proof_of_checked_mul_return_wit_10 : checked_mul_return_wit_10.
Axiom proof_of_checked_mul_return_wit_11 : checked_mul_return_wit_11.
Axiom proof_of_checked_mul_return_wit_12 : checked_mul_return_wit_12.
Axiom proof_of_checked_mul_return_wit_13 : checked_mul_return_wit_13.
Axiom proof_of_checked_mul_return_wit_14 : checked_mul_return_wit_14.
Axiom proof_of_checked_mul_return_wit_15 : checked_mul_return_wit_15.
Axiom proof_of_checked_mul_return_wit_16 : checked_mul_return_wit_16.
Axiom proof_of_checked_mul_return_wit_17 : checked_mul_return_wit_17.
Axiom proof_of_checked_mul_return_wit_18 : checked_mul_return_wit_18.
Axiom proof_of_checked_mul_return_wit_19 : checked_mul_return_wit_19.
Axiom proof_of_checked_mul_return_wit_20 : checked_mul_return_wit_20.
Axiom proof_of_checked_mul_return_wit_21 : checked_mul_return_wit_21.
Axiom proof_of_checked_mul_return_wit_22 : checked_mul_return_wit_22.
Axiom proof_of_checked_mul_return_wit_23 : checked_mul_return_wit_23.
Axiom proof_of_checked_mul_return_wit_24 : checked_mul_return_wit_24.

End VC_Correct.
