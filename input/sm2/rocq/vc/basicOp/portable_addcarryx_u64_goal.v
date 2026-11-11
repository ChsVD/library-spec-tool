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
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope sac.

(*----- Function portable_addcarryx_u64 -----*)

Definition portable_addcarryx_u64_safety_wit_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH2 : (0 <= carry_in_pre)) (PreH3 : (carry_in_pre <= 1)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre < U64_MOD)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre < U64_MOD)) ,
  ((( &( "carry1" ) )) # UChar  |->_)
  **  ((( &( "sum" ) )) # UInt64  |-> (unsigned_last_nbits ((a_pre + b_pre )) (64)))
  **  ((( &( "carry_in" ) )) # UChar  |-> carry_in_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((result_pre) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition portable_addcarryx_u64_safety_wit_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH2 : (0 <= carry_in_pre)) (PreH3 : (carry_in_pre <= 1)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre < U64_MOD)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre < U64_MOD)) ,
  ((( &( "carry1" ) )) # UChar  |->_)
  **  ((( &( "sum" ) )) # UInt64  |-> (unsigned_last_nbits ((a_pre + b_pre )) (64)))
  **  ((( &( "carry_in" ) )) # UChar  |-> carry_in_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((result_pre) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition portable_addcarryx_u64_safety_wit_3 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((( &( "carry2" ) )) # UChar  |->_)
  **  ((( &( "sum2" ) )) # UInt64  |-> ((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ))
  **  ((( &( "carry1" ) )) # UChar  |-> 1)
  **  ((( &( "sum" ) )) # UInt64  |-> (unsigned_last_nbits ((a_pre + b_pre )) (64)))
  **  ((( &( "carry_in" ) )) # UChar  |-> carry_in_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((result_pre) # UInt64  |->_)
|--
  “ False ”
.

Definition portable_addcarryx_u64_safety_wit_4 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((( &( "carry2" ) )) # UChar  |->_)
  **  ((( &( "sum2" ) )) # UInt64  |-> ((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ))
  **  ((( &( "carry1" ) )) # UChar  |-> 1)
  **  ((( &( "sum" ) )) # UInt64  |-> (unsigned_last_nbits ((a_pre + b_pre )) (64)))
  **  ((( &( "carry_in" ) )) # UChar  |-> carry_in_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((result_pre) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition portable_addcarryx_u64_safety_wit_5 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((( &( "carry2" ) )) # UChar  |->_)
  **  ((( &( "sum2" ) )) # UInt64  |-> (unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)))
  **  ((( &( "carry1" ) )) # UChar  |-> 0)
  **  ((( &( "sum" ) )) # UInt64  |-> (unsigned_last_nbits ((a_pre + b_pre )) (64)))
  **  ((( &( "carry_in" ) )) # UChar  |-> carry_in_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((result_pre) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition portable_addcarryx_u64_safety_wit_6 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((( &( "carry2" ) )) # UChar  |->_)
  **  ((( &( "sum2" ) )) # UInt64  |-> (unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)))
  **  ((( &( "carry1" ) )) # UChar  |-> 0)
  **  ((( &( "sum" ) )) # UInt64  |-> (unsigned_last_nbits ((a_pre + b_pre )) (64)))
  **  ((( &( "carry_in" ) )) # UChar  |-> carry_in_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((result_pre) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition portable_addcarryx_u64_return_wit_1 := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((result_pre) # UInt64  |-> ((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ))
|--
  EX (out: Z) ,
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= (Z.lor 1 0)) ” 
  &&  “ ((Z.lor 1 0) <= 1) ” 
  &&  “ (((a_pre + b_pre ) + carry_in_pre ) = (out + ((Z.lor 1 0) * U64_MOD ) )) ”
  &&  ((result_pre) # UInt64  |-> out)
) \/
(
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ (((a_pre + b_pre ) + carry_in_pre ) = (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) + ((Z.lor 1 0) * U64_MOD ) )) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) ”
  &&  emp
).

Definition portable_addcarryx_u64_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  (((a_pre + b_pre ) + carry_in_pre ) = (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) + ((Z.lor 1 0) * U64_MOD ) ))
.

Definition portable_addcarryx_u64_return_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) < a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  (0 <= ((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre ))
.

Definition portable_addcarryx_u64_return_wit_2 := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((result_pre) # UInt64  |-> (unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)))
|--
  EX (out: Z) ,
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= (Z.lor 0 1)) ” 
  &&  “ ((Z.lor 0 1) <= 1) ” 
  &&  “ (((a_pre + b_pre ) + carry_in_pre ) = (out + ((Z.lor 0 1) * U64_MOD ) )) ”
  &&  ((result_pre) # UInt64  |-> out)
) \/
(
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ (((a_pre + b_pre ) + carry_in_pre ) = ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) + ((Z.lor 0 1) * U64_MOD ) )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64))) ”
  &&  emp
).

Definition portable_addcarryx_u64_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  (((a_pre + b_pre ) + carry_in_pre ) = ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) + ((Z.lor 0 1) * U64_MOD ) ))
.

Definition portable_addcarryx_u64_return_wit_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < U64_MOD)
.

Definition portable_addcarryx_u64_return_wit_2_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)))
.

Definition portable_addcarryx_u64_return_wit_3 := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((result_pre) # UInt64  |-> (unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)))
|--
  EX (out: Z) ,
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= (Z.lor 0 0)) ” 
  &&  “ ((Z.lor 0 0) <= 1) ” 
  &&  “ (((a_pre + b_pre ) + carry_in_pre ) = (out + ((Z.lor 0 0) * U64_MOD ) )) ”
  &&  ((result_pre) # UInt64  |-> out)
) \/
(
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ (((a_pre + b_pre ) + carry_in_pre ) = ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) + ((Z.lor 0 0) * U64_MOD ) )) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < U64_MOD) ”
  &&  emp
).

Definition portable_addcarryx_u64_return_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  (((a_pre + b_pre ) + carry_in_pre ) = ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) + ((Z.lor 0 0) * U64_MOD ) ))
.

Definition portable_addcarryx_u64_return_wit_3_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (carry_in_pre: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) >= (unsigned_last_nbits ((a_pre + b_pre )) (64)))) (PreH2 : ((unsigned_last_nbits ((a_pre + b_pre )) (64)) >= a_pre)) (PreH3 : (0 <= carry_in_pre)) (PreH4 : (carry_in_pre <= 1)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre < U64_MOD)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits (((unsigned_last_nbits ((a_pre + b_pre )) (64)) + carry_in_pre )) (64)) < U64_MOD)
.

Module Type VC_Correct.


Axiom proof_of_portable_addcarryx_u64_safety_wit_1 : portable_addcarryx_u64_safety_wit_1.
Axiom proof_of_portable_addcarryx_u64_safety_wit_2 : portable_addcarryx_u64_safety_wit_2.
Axiom proof_of_portable_addcarryx_u64_safety_wit_3 : portable_addcarryx_u64_safety_wit_3.
Axiom proof_of_portable_addcarryx_u64_safety_wit_4 : portable_addcarryx_u64_safety_wit_4.
Axiom proof_of_portable_addcarryx_u64_safety_wit_5 : portable_addcarryx_u64_safety_wit_5.
Axiom proof_of_portable_addcarryx_u64_safety_wit_6 : portable_addcarryx_u64_safety_wit_6.
Axiom proof_of_portable_addcarryx_u64_return_wit_1 : portable_addcarryx_u64_return_wit_1.
Axiom proof_of_portable_addcarryx_u64_return_wit_2 : portable_addcarryx_u64_return_wit_2.
Axiom proof_of_portable_addcarryx_u64_return_wit_3 : portable_addcarryx_u64_return_wit_3.

End VC_Correct.
