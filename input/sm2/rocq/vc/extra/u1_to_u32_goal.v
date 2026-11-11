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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.

(*----- Function u1_to_u32 -----*)

Definition u1_to_u32_safety_wit_1 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) ,
  (UCharArray.undef_full ( &( "tmp" ) ) 32 )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u1_to_u32_safety_wit_2 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) ,
  (UCharArray.undef_full ( &( "tmp" ) ) 32 )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition u1_to_u32_safety_wit_3 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 bytes )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u1_to_u32_safety_wit_4 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 bytes )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition u1_to_u32_safety_wit_5 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (aligned_4 result_pre )) (PreH2 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (UCharArray.undef_full result_pre 32 )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u1_to_u32_safety_wit_6 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (aligned_4 result_pre )) (PreH2 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (UCharArray.undef_full result_pre 32 )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition u1_to_u32_entail_wit_1 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
|--
  “ (aligned_4 result_pre ) ” 
  &&  “ (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR)))) ”
  &&  (UCharArray.undef_full result_pre 32 )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition u1_to_u32_entail_wit_2 := 
(
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = result_pre)) (PreH2 : (aligned_4 result_pre )) (PreH3 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes result_pre 32 (rev (bytes)) )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
|--
  “ ((u8_list_value ((rev (bytes)))) = (be_u8_list_value (bytes))) ” 
  &&  “ (retval_2 = result_pre) ” 
  &&  “ (aligned_4 result_pre ) ” 
  &&  “ (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR)))) ”
  &&  (store_bytes result_pre 32 (rev (bytes)) )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
) \/
(
forall (result_pre: Z) (bytes: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = result_pre)) (PreH2 : (aligned_4 result_pre )) (PreH3 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  TT && emp 
|--
  “ ((u8_list_value ((rev (bytes)))) = (be_u8_list_value (bytes))) ”
  &&  emp
).

Definition u1_to_u32_entail_wit_2_split_goal_1 := 
forall (result_pre: Z) (bytes: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = result_pre)) (PreH2 : (aligned_4 result_pre )) (PreH3 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  ((u8_list_value ((rev (bytes)))) = (be_u8_list_value (bytes)))
.

Definition u1_to_u32_entail_wit_3 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((u8_list_value ((rev (bytes)))) = (be_u8_list_value (bytes)))) (PreH2 : (retval_2 = result_pre)) (PreH3 : (aligned_4 result_pre )) (PreH4 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes result_pre 32 (rev (bytes)) )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((u8_list_value ((rev (bytes)))) = (be_u8_list_value (bytes))) ” 
  &&  “ (retval_2 = result_pre) ” 
  &&  “ (aligned_4 result_pre ) ” 
  &&  “ (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR)))) ”
  &&  (store_u256 result_pre (be_u8_list_value (bytes)) )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition u1_to_u32_return_wit_1 := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : ((u8_list_value ((rev (bytes)))) = (be_u8_list_value (bytes)))) (PreH2 : (retval_2 = result_pre)) (PreH3 : (aligned_4 result_pre )) (PreH4 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_u256 result_pre (be_u8_list_value (bytes)) )
  **  (store_bytes input_pre 32 bytes )
|--
  (store_bytes input_pre 32 bytes )
  **  (store_u256 result_pre (be_u8_list_value (bytes)) )
.

Definition u1_to_u32_partial_solve_wit_1_pure := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) ,
  (UCharArray.undef_full ( &( "tmp" ) ) 32 )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 <= 32) ”
.

Definition u1_to_u32_partial_solve_wit_1_aux := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) ,
  (UCharArray.undef_full ( &( "tmp" ) ) 32 )
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 <= 32) ”
  &&  (UCharArray.undef_full (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
.

Definition u1_to_u32_partial_solve_wit_1 := u1_to_u32_partial_solve_wit_1_pure -> u1_to_u32_partial_solve_wit_1_aux.

Definition u1_to_u32_partial_solve_wit_2_pure := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 bytes )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 < 32) ”
.

Definition u1_to_u32_partial_solve_wit_2_aux := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 bytes )
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 < 32) ” 
  &&  “ (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR)))) ”
  &&  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 bytes )
  **  (store_bytes input_pre 32 bytes )
  **  (UndefStructPredu32 result_pre )
.

Definition u1_to_u32_partial_solve_wit_2 := u1_to_u32_partial_solve_wit_2_pure -> u1_to_u32_partial_solve_wit_2_aux.

Definition u1_to_u32_partial_solve_wit_3_pure := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (aligned_4 result_pre )) (PreH2 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (UCharArray.undef_full result_pre 32 )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 32) ”
.

Definition u1_to_u32_partial_solve_wit_3_aux := 
forall (result_pre: Z) (input_pre: Z) (bytes: (@list Z)) (retval: Z) (PreH1 : (aligned_4 result_pre )) (PreH2 : (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR))))) ,
  (UCharArray.undef_full result_pre 32 )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
|--
  “ (0 <= 32) ” 
  &&  “ (aligned_4 result_pre ) ” 
  &&  “ (retval = (( &( "tmp" ) ) + (0 * sizeof(UCHAR)))) ”
  &&  (UCharArray.undef_full result_pre 32 )
  **  (store_bytes (( &( "tmp" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (store_bytes input_pre 32 bytes )
.

Definition u1_to_u32_partial_solve_wit_3 := u1_to_u32_partial_solve_wit_3_pure -> u1_to_u32_partial_solve_wit_3_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include byte_memory_views_Strategy_Correct.

Axiom proof_of_u1_to_u32_safety_wit_1 : u1_to_u32_safety_wit_1.
Axiom proof_of_u1_to_u32_safety_wit_2 : u1_to_u32_safety_wit_2.
Axiom proof_of_u1_to_u32_safety_wit_3 : u1_to_u32_safety_wit_3.
Axiom proof_of_u1_to_u32_safety_wit_4 : u1_to_u32_safety_wit_4.
Axiom proof_of_u1_to_u32_safety_wit_5 : u1_to_u32_safety_wit_5.
Axiom proof_of_u1_to_u32_safety_wit_6 : u1_to_u32_safety_wit_6.
Axiom proof_of_u1_to_u32_entail_wit_1 : u1_to_u32_entail_wit_1.
Axiom proof_of_u1_to_u32_entail_wit_2 : u1_to_u32_entail_wit_2.
Axiom proof_of_u1_to_u32_entail_wit_3 : u1_to_u32_entail_wit_3.
Axiom proof_of_u1_to_u32_return_wit_1 : u1_to_u32_return_wit_1.
Axiom proof_of_u1_to_u32_partial_solve_wit_1_pure : u1_to_u32_partial_solve_wit_1_pure.
Axiom proof_of_u1_to_u32_partial_solve_wit_1 : u1_to_u32_partial_solve_wit_1.
Axiom proof_of_u1_to_u32_partial_solve_wit_2_pure : u1_to_u32_partial_solve_wit_2_pure.
Axiom proof_of_u1_to_u32_partial_solve_wit_2 : u1_to_u32_partial_solve_wit_2.
Axiom proof_of_u1_to_u32_partial_solve_wit_3_pure : u1_to_u32_partial_solve_wit_3_pure.
Axiom proof_of_u1_to_u32_partial_solve_wit_3 : u1_to_u32_partial_solve_wit_3.

End VC_Correct.
