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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_pointer_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_pointer_views_strategy_proof.

(*----- Function str_reverse_in_place -----*)

Definition str_reverse_in_place_safety_wit_1 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (PreH1 : (0 < len_pre)) ,
  ((( &( "p2" ) )) # Ptr  |->_)
  **  ((( &( "p1" ) )) # Ptr  |-> str_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
  **  (store_bytes str_pre len_pre bytes )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition str_reverse_in_place_entail_wit_1 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (PreH1 : (0 < len_pre)) ,
  ((( &( "p2" ) )) # Ptr  |-> (str_pre + ((len_pre + (-1) ) * sizeof(UCHAR))))
  **  ((( &( "p1" ) )) # Ptr  |-> str_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
  **  (store_bytes str_pre len_pre bytes )
|--
  “ (u8_list_bounded bytes ) ” 
  &&  “ ((Zlength (bytes)) = len_pre) ” 
  &&  “ (0 < len_pre) ”
  &&  (UCharArray.full str_pre len_pre bytes )
  **  ((( &( "p2" ) )) # Ptr  |-> (str_pre + ((len_pre + (-1) ) * sizeof(UCHAR))))
  **  ((( &( "p1" ) )) # Ptr  |-> str_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
.

Definition str_reverse_in_place_entail_wit_2 := 
(
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (PreH1 : (u8_list_bounded bytes )) (PreH2 : ((Zlength (bytes)) = len_pre)) (PreH3 : (0 < len_pre)) ,
  (UCharArray.full str_pre len_pre bytes )
|--
  EX (current: (@list Z))  (index: Z) ,
  “ (str_pre = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ ((str_pre + ((len_pre + (-1) ) * sizeof(UCHAR))) = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (current)) = len_pre) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (0 < len_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < len_pre) ” 
  &&  “ ((2 * index ) <= len_pre) ” 
  &&  “ (byte_reverse_loop_state bytes current index ) ”
  &&  (UCharArray.full str_pre len_pre current )
) \/
(
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (PreH1 : (u8_list_bounded bytes )) (PreH2 : ((Zlength (bytes)) = len_pre)) (PreH3 : (0 < len_pre)) ,
  TT && emp 
|--
  EX (index: Z) ,
  “ (str_pre = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ ((str_pre + (((Zlength (bytes)) + (-1) ) * sizeof(UCHAR))) = (str_pre + ((((Zlength (bytes)) - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < (Zlength (bytes))) ” 
  &&  “ ((2 * index ) <= (Zlength (bytes))) ” 
  &&  “ (byte_reverse_loop_state bytes bytes index ) ”
  &&  emp
).

Definition str_reverse_in_place_entail_wit_3 := 
(
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (p2: Z) (p1: Z) (current_2: (@list Z)) (index_2: Z) (PreH1 : (p1 < p2)) (PreH2 : (p1 = (str_pre + (index_2 * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index_2 ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current_2)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index_2)) (PreH8 : (index_2 < len_pre)) (PreH9 : ((2 * index_2 ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current_2 index_2 )) ,
  (UCharArray.full str_pre len_pre (replace_Znth (((len_pre - 1 ) - index_2 )) ((Znth (index_2) (current_2) (0))) ((replace_Znth (index_2) ((Znth (((len_pre - 1 ) - index_2 )) (current_2) (0))) (current_2)))) )
|--
  EX (current: (@list Z))  (index: Z) ,
  “ ((p1 + (1 * sizeof(UCHAR))) = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ ((p2 + ((-1) * sizeof(UCHAR))) = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (current)) = len_pre) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (0 < len_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < len_pre) ” 
  &&  “ ((2 * index ) <= len_pre) ” 
  &&  “ (byte_reverse_loop_state bytes current index ) ”
  &&  (UCharArray.full str_pre len_pre current )
) \/
(
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (p2: Z) (p1: Z) (current_2: (@list Z)) (index_2: Z) (PreH1 : (p1 < p2)) (PreH2 : (p1 = (str_pre + (index_2 * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index_2 ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current_2)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index_2)) (PreH8 : (index_2 < len_pre)) (PreH9 : ((2 * index_2 ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current_2 index_2 )) ,
  TT && emp 
|--
  EX (index: Z) ,
  “ (((str_pre + (index_2 * sizeof(UCHAR))) + (1 * sizeof(UCHAR))) = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ (((str_pre + ((((Zlength (current_2)) - 1 ) - index_2 ) * sizeof(UCHAR))) + ((-1) * sizeof(UCHAR))) = (str_pre + ((((Zlength (current_2)) - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((replace_Znth ((((Zlength (current_2)) - 1 ) - index_2 )) ((Znth (index_2) (current_2) (0))) ((replace_Znth (index_2) ((Znth ((((Zlength (current_2)) - 1 ) - index_2 )) (current_2) (0))) (current_2)))))) = (Zlength (current_2))) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < (Zlength (current_2))) ” 
  &&  “ ((2 * index ) <= (Zlength (current_2))) ” 
  &&  “ (byte_reverse_loop_state bytes (replace_Znth ((((Zlength (current_2)) - 1 ) - index_2 )) ((Znth (index_2) (current_2) (0))) ((replace_Znth (index_2) ((Znth ((((Zlength (current_2)) - 1 ) - index_2 )) (current_2) (0))) (current_2)))) index ) ”
  &&  emp
).

Definition str_reverse_in_place_return_wit_1 := 
(
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (current: (@list Z)) (p2: Z) (index: Z) (p1: Z) (PreH1 : (p1 >= p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (UCharArray.full str_pre len_pre current )
|--
  (store_bytes str_pre len_pre (rev (bytes)) )
) \/
(
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (current: (@list Z)) (p2: Z) (index: Z) (p1: Z) (PreH1 : (p1 >= p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  TT && emp 
|--
  “ ((Zlength ((rev (bytes)))) = len_pre) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ (current = (rev (bytes))) ”
  &&  emp
).

Definition str_reverse_in_place_return_wit_1_split_goal_1 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (current: (@list Z)) (p2: Z) (index: Z) (p1: Z) (PreH1 : (p1 >= p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  ((Zlength ((rev (bytes)))) = len_pre)
.

Definition str_reverse_in_place_return_wit_1_split_goal_2 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (current: (@list Z)) (p2: Z) (index: Z) (p1: Z) (PreH1 : (p1 >= p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (u8_list_bounded (rev (bytes)) )
.

Definition str_reverse_in_place_return_wit_1_split_goal_3 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (current: (@list Z)) (p2: Z) (index: Z) (p1: Z) (PreH1 : (p1 >= p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (current = (rev (bytes)))
.

Definition str_reverse_in_place_partial_solve_wit_1 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (p2: Z) (p1: Z) (current: (@list Z)) (index: Z) (PreH1 : (p1 < p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (UCharArray.full str_pre len_pre current )
|--
  “ (p1 < p2) ” 
  &&  “ (p1 = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (current)) = len_pre) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (0 < len_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < len_pre) ” 
  &&  “ ((2 * index ) <= len_pre) ” 
  &&  “ (byte_reverse_loop_state bytes current index ) ”
  &&  ((p1) # UChar  |-> (Znth (index) (current) (0)))
  **  (UCharArray.missing_i str_pre index 0 len_pre current )
.

Definition str_reverse_in_place_partial_solve_wit_2 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (p2: Z) (p1: Z) (current: (@list Z)) (index: Z) (PreH1 : (p1 < p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (UCharArray.full str_pre len_pre current )
|--
  “ (p1 < p2) ” 
  &&  “ (p1 = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (current)) = len_pre) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (0 < len_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < len_pre) ” 
  &&  “ ((2 * index ) <= len_pre) ” 
  &&  “ (byte_reverse_loop_state bytes current index ) ”
  &&  ((p2) # UChar  |-> (Znth (((len_pre - 1 ) - index )) (current) (0)))
  **  (UCharArray.missing_i str_pre ((len_pre - 1 ) - index ) 0 len_pre current )
.

Definition str_reverse_in_place_partial_solve_wit_3 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (p2: Z) (p1: Z) (current: (@list Z)) (index: Z) (PreH1 : (p1 < p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (UCharArray.full str_pre len_pre current )
|--
  “ (p1 < p2) ” 
  &&  “ (p1 = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (current)) = len_pre) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (0 < len_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < len_pre) ” 
  &&  “ ((2 * index ) <= len_pre) ” 
  &&  “ (byte_reverse_loop_state bytes current index ) ”
  &&  ((p1) # UChar  |->_)
  **  (UCharArray.missing_i str_pre index 0 len_pre current )
.

Definition str_reverse_in_place_partial_solve_wit_4 := 
forall (len_pre: Z) (str_pre: Z) (bytes: (@list Z)) (p2: Z) (p1: Z) (current: (@list Z)) (index: Z) (PreH1 : (p1 < p2)) (PreH2 : (p1 = (str_pre + (index * sizeof(UCHAR))))) (PreH3 : (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR))))) (PreH4 : ((Zlength (current)) = len_pre)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (0 < len_pre)) (PreH7 : (0 <= index)) (PreH8 : (index < len_pre)) (PreH9 : ((2 * index ) <= len_pre)) (PreH10 : (byte_reverse_loop_state bytes current index )) ,
  (UCharArray.full str_pre len_pre (replace_Znth (index) ((Znth (((len_pre - 1 ) - index )) (current) (0))) (current)) )
|--
  “ (p1 < p2) ” 
  &&  “ (p1 = (str_pre + (index * sizeof(UCHAR)))) ” 
  &&  “ (p2 = (str_pre + (((len_pre - 1 ) - index ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (current)) = len_pre) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (0 < len_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < len_pre) ” 
  &&  “ ((2 * index ) <= len_pre) ” 
  &&  “ (byte_reverse_loop_state bytes current index ) ”
  &&  ((p2) # UChar  |->_)
  **  (UCharArray.missing_i str_pre ((len_pre - 1 ) - index ) 0 len_pre (replace_Znth (index) ((Znth (((len_pre - 1 ) - index )) (current) (0))) (current)) )
.

Module Type VC_Correct.

Include byte_memory_views_Strategy_Correct.
Include byte_pointer_views_Strategy_Correct.

Axiom proof_of_str_reverse_in_place_safety_wit_1 : str_reverse_in_place_safety_wit_1.
Axiom proof_of_str_reverse_in_place_entail_wit_1 : str_reverse_in_place_entail_wit_1.
Axiom proof_of_str_reverse_in_place_entail_wit_2 : str_reverse_in_place_entail_wit_2.
Axiom proof_of_str_reverse_in_place_entail_wit_3 : str_reverse_in_place_entail_wit_3.
Axiom proof_of_str_reverse_in_place_return_wit_1 : str_reverse_in_place_return_wit_1.
Axiom proof_of_str_reverse_in_place_partial_solve_wit_1 : str_reverse_in_place_partial_solve_wit_1.
Axiom proof_of_str_reverse_in_place_partial_solve_wit_2 : str_reverse_in_place_partial_solve_wit_2.
Axiom proof_of_str_reverse_in_place_partial_solve_wit_3 : str_reverse_in_place_partial_solve_wit_3.
Axiom proof_of_str_reverse_in_place_partial_solve_wit_4 : str_reverse_in_place_partial_solve_wit_4.

End VC_Correct.
