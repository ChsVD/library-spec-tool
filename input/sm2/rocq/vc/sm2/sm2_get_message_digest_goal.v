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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_get_message_digest -----*)

Definition sm2_get_message_digest_safety_wit_1 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_message_digest_safety_wit_2 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (sm3_ctx_full_shape ( &( "ctx" ) ) )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((app ((app ((@nil Z)) (ZABytes))) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_message_digest_return_wit_1 := 
(
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_bytes result_pre 32 (sm3_digest_bytes ((app ((app ((@nil Z)) (ZABytes))) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_bytes ZA_pre 32 ZABytes )
|--
  “ (0 = 0) ”
  &&  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((app (ZABytes) (Message)))) )
  **  (store_sm3_ti )
) \/
(
forall (msg_len_pre: Z) (msg_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  TT && emp 
|--
  “ ((sm3_digest_bytes ((app ((app ((@nil Z)) (ZABytes))) (Message)))) = (sm3_digest_bytes ((app (ZABytes) (Message))))) ”
  &&  emp
).

Definition sm2_get_message_digest_return_wit_1_split_goal_1 := 
forall (msg_len_pre: Z) (msg_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  ((sm3_digest_bytes ((app ((app ((@nil Z)) (ZABytes))) (Message)))) = (sm3_digest_bytes ((app (ZABytes) (Message)))))
.

Definition sm2_get_message_digest_partial_solve_wit_1 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (UndefStructPred_SM3_CTX ( &( "ctx" ) ) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 result_pre ) ”
  &&  (undef_sm3_ctx ( &( "ctx" ) ) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
.

Definition sm2_get_message_digest_partial_solve_wit_2_pure := 
(
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_update_data_aligned ZA_pre 32 (Zlength ((sm3_tail ((@nil Z))))) ) ” 
  &&  “ (((Zlength ((@nil Z))) + 32 ) < SM3_MAX_BYTES) ”
) \/
(
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (msg_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre >= 0)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH4 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (((Zlength ((@nil Z))) + 32 ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned ZA_pre 32 (Zlength ((sm3_tail ((@nil Z))))) ) ”
).

Definition sm2_get_message_digest_partial_solve_wit_2_pure_split_goal_1 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (msg_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre >= 0)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH4 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (((Zlength ((@nil Z))) + 32 ) < SM3_MAX_BYTES) ”
.

Definition sm2_get_message_digest_partial_solve_wit_2_pure_split_goal_2 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (msg_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre >= 0)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH4 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_update_data_aligned ZA_pre 32 (Zlength ((sm3_tail ((@nil Z))))) ) ”
.

Definition sm2_get_message_digest_partial_solve_wit_2_aux := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_update_data_aligned ZA_pre 32 (Zlength ((sm3_tail ((@nil Z))))) ) ” 
  &&  “ (((Zlength ((@nil Z))) + 32 ) < SM3_MAX_BYTES) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 result_pre ) ”
  &&  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_sm3_ti )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_message_digest_partial_solve_wit_2 := sm2_get_message_digest_partial_solve_wit_2_pure -> sm2_get_message_digest_partial_solve_wit_2_aux.

Definition sm2_get_message_digest_partial_solve_wit_3_pure := 
(
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (ZABytes)) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (sm3_update_data_aligned msg_pre msg_len_pre (Zlength ((sm3_tail ((app ((@nil Z)) (ZABytes)))))) ) ” 
  &&  “ (((Zlength ((app ((@nil Z)) (ZABytes)))) + msg_len_pre ) < SM3_MAX_BYTES) ”
) \/
(
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (msg_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre >= 0)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH4 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (ZABytes)) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (((Zlength ((app ((@nil Z)) (ZABytes)))) + msg_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned msg_pre msg_len_pre (Zlength ((sm3_tail ((app ((@nil Z)) (ZABytes)))))) ) ”
).

Definition sm2_get_message_digest_partial_solve_wit_3_pure_split_goal_1 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (msg_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre >= 0)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH4 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (ZABytes)) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (((Zlength ((app ((@nil Z)) (ZABytes)))) + msg_len_pre ) < SM3_MAX_BYTES) ”
.

Definition sm2_get_message_digest_partial_solve_wit_3_pure_split_goal_2 := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (msg_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre >= 0)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH4 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (ZABytes)) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (sm3_update_data_aligned msg_pre msg_len_pre (Zlength ((sm3_tail ((app ((@nil Z)) (ZABytes)))))) ) ”
.

Definition sm2_get_message_digest_partial_solve_wit_3_aux := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (ZABytes)) )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (store_sm3_ti )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (sm3_update_data_aligned msg_pre msg_len_pre (Zlength ((sm3_tail ((app ((@nil Z)) (ZABytes)))))) ) ” 
  &&  “ (((Zlength ((app ((@nil Z)) (ZABytes)))) + msg_len_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 result_pre ) ”
  &&  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (ZABytes)) )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_sm3_ti )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_message_digest_partial_solve_wit_3 := sm2_get_message_digest_partial_solve_wit_3_pure -> sm2_get_message_digest_partial_solve_wit_3_aux.

Definition sm2_get_message_digest_partial_solve_wit_4_pure := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((app ((@nil Z)) (ZABytes))) (Message)) )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_sm3_ti )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "ZA" ) )) # Ptr  |-> ZA_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 result_pre ) ”
.

Definition sm2_get_message_digest_partial_solve_wit_4_aux := 
forall (msg_len_pre: Z) (msg_pre: Z) (ZA_pre: Z) (result_pre: Z) (Message: (@list Z)) (ZABytes: (@list Z)) (PreH1 : (sm2_message_input_aligned msg_pre msg_len_pre )) (PreH2 : (aligned_4 result_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((app ((@nil Z)) (ZABytes))) (Message)) )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_sm3_ti )
  **  (store_bytes ZA_pre 32 ZABytes )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 result_pre ) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 result_pre ) ”
  &&  (store_sm3_ctx ( &( "ctx" ) ) (app ((app ((@nil Z)) (ZABytes))) (Message)) )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
  **  (store_bytes msg_pre msg_len_pre Message )
  **  (store_bytes ZA_pre 32 ZABytes )
.

Definition sm2_get_message_digest_partial_solve_wit_4 := sm2_get_message_digest_partial_solve_wit_4_pure -> sm2_get_message_digest_partial_solve_wit_4_aux.

Module Type VC_Correct.

Include byte_memory_views_Strategy_Correct.
Include sm3_ctx_views_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_get_message_digest_safety_wit_1 : sm2_get_message_digest_safety_wit_1.
Axiom proof_of_sm2_get_message_digest_safety_wit_2 : sm2_get_message_digest_safety_wit_2.
Axiom proof_of_sm2_get_message_digest_return_wit_1 : sm2_get_message_digest_return_wit_1.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_1 : sm2_get_message_digest_partial_solve_wit_1.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_2_pure : sm2_get_message_digest_partial_solve_wit_2_pure.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_2 : sm2_get_message_digest_partial_solve_wit_2.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_3_pure : sm2_get_message_digest_partial_solve_wit_3_pure.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_3 : sm2_get_message_digest_partial_solve_wit_3.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_4_pure : sm2_get_message_digest_partial_solve_wit_4_pure.
Axiom proof_of_sm2_get_message_digest_partial_solve_wit_4 : sm2_get_message_digest_partial_solve_wit_4.

End VC_Correct.
