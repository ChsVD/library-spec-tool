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
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_proof.

(*----- Function sm3 -----*)

Definition sm3_safety_wit_1 := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (sm3_ctx_full_shape ( &( "ctx" ) ) )
  **  (store_bytes dgst_pre 32 (sm3_digest_bytes ((app ((@nil Z)) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_safety_wit_2 := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (retval: Z) (PreH1 : (retval = ( &( "ctx" ) ))) (PreH2 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH3 : (aligned_4 dgst_pre )) ,
  (sm3_ctx_full_shape ( &( "ctx" ) ) )
  **  (store_bytes dgst_pre 32 (sm3_digest_bytes ((app ((@nil Z)) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm3_return_wit_1 := 
(
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (retval: Z) (PreH1 : (retval = ( &( "ctx" ) ))) (PreH2 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH3 : (aligned_4 dgst_pre )) ,
  (store_bytes dgst_pre 32 (sm3_digest_bytes ((app ((@nil Z)) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
|--
  “ (32 = 32) ”
  &&  (store_bytes data_pre datalen_pre Message )
  **  (store_bytes dgst_pre 32 (sm3_digest_bytes (Message)) )
  **  (store_sm3_ti )
) \/
(
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (retval: Z) (PreH1 : (retval = ( &( "ctx" ) ))) (PreH2 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH3 : (aligned_4 dgst_pre )) ,
  TT && emp 
|--
  “ ((sm3_digest_bytes ((app ((@nil Z)) (Message)))) = (sm3_digest_bytes (Message))) ”
  &&  emp
).

Definition sm3_return_wit_1_split_goal_1 := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (retval: Z) (PreH1 : (retval = ( &( "ctx" ) ))) (PreH2 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH3 : (aligned_4 dgst_pre )) ,
  ((sm3_digest_bytes ((app ((@nil Z)) (Message)))) = (sm3_digest_bytes (Message)))
.

Definition sm3_partial_solve_wit_1 := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (UndefStructPred_SM3_CTX ( &( "ctx" ) ) )
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_digest_input_aligned data_pre datalen_pre ) ” 
  &&  “ (aligned_4 dgst_pre ) ”
  &&  (undef_sm3_ctx ( &( "ctx" ) ) )
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
.

Definition sm3_partial_solve_wit_2_pure := 
(
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_update_data_aligned data_pre datalen_pre (Zlength ((sm3_tail ((@nil Z))))) ) ” 
  &&  “ (((Zlength ((@nil Z))) + datalen_pre ) < SM3_MAX_BYTES) ”
) \/
(
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (datalen_pre <= UINT64_MAX)) (PreH2 : (datalen_pre >= 0)) (PreH3 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH4 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
|--
  “ (((Zlength ((@nil Z))) + datalen_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_update_data_aligned data_pre datalen_pre (Zlength ((sm3_tail ((@nil Z))))) ) ”
).

Definition sm3_partial_solve_wit_2_pure_split_goal_1 := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (datalen_pre <= UINT64_MAX)) (PreH2 : (datalen_pre >= 0)) (PreH3 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH4 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
|--
  “ (((Zlength ((@nil Z))) + datalen_pre ) < SM3_MAX_BYTES) ”
.

Definition sm3_partial_solve_wit_2_pure_split_goal_2 := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (datalen_pre <= UINT64_MAX)) (PreH2 : (datalen_pre >= 0)) (PreH3 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH4 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_update_data_aligned data_pre datalen_pre (Zlength ((sm3_tail ((@nil Z))))) ) ”
.

Definition sm3_partial_solve_wit_2_aux := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  (store_bytes data_pre datalen_pre Message )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
|--
  “ (sm3_update_data_aligned data_pre datalen_pre (Zlength ((sm3_tail ((@nil Z))))) ) ” 
  &&  “ (((Zlength ((@nil Z))) + datalen_pre ) < SM3_MAX_BYTES) ” 
  &&  “ (sm3_digest_input_aligned data_pre datalen_pre ) ” 
  &&  “ (aligned_4 dgst_pre ) ”
  &&  (store_sm3_ctx ( &( "ctx" ) ) (@nil Z) )
  **  (store_bytes data_pre datalen_pre Message )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full dgst_pre 32 )
.

Definition sm3_partial_solve_wit_2 := sm3_partial_solve_wit_2_pure -> sm3_partial_solve_wit_2_aux.

Definition sm3_partial_solve_wit_3_pure := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (Message)) )
  **  (store_bytes data_pre datalen_pre Message )
  **  (store_sm3_ti )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  (UCharArray.undef_full dgst_pre 32 )
|--
  “ (aligned_4 dgst_pre ) ”
.

Definition sm3_partial_solve_wit_3_aux := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (Message)) )
  **  (store_bytes data_pre datalen_pre Message )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full dgst_pre 32 )
|--
  “ (aligned_4 dgst_pre ) ” 
  &&  “ (sm3_digest_input_aligned data_pre datalen_pre ) ” 
  &&  “ (aligned_4 dgst_pre ) ”
  &&  (store_sm3_ctx ( &( "ctx" ) ) (app ((@nil Z)) (Message)) )
  **  (UCharArray.undef_full dgst_pre 32 )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
.

Definition sm3_partial_solve_wit_3 := sm3_partial_solve_wit_3_pure -> sm3_partial_solve_wit_3_aux.

Definition sm3_partial_solve_wit_4_pure := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (sm3_ctx_full_shape ( &( "ctx" ) ) )
  **  (store_bytes dgst_pre 32 (sm3_digest_bytes ((app ((@nil Z)) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "datalen" ) )) # UInt64  |-> datalen_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
|--
  “ (sizeof( "_SM3_CTX" ) = sizeof( "_SM3_CTX" )) ”
.

Definition sm3_partial_solve_wit_4_aux := 
forall (dgst_pre: Z) (datalen_pre: Z) (data_pre: Z) (Message: (@list Z)) (PreH1 : (sm3_digest_input_aligned data_pre datalen_pre )) (PreH2 : (aligned_4 dgst_pre )) ,
  (sm3_ctx_full_shape ( &( "ctx" ) ) )
  **  (store_bytes dgst_pre 32 (sm3_digest_bytes ((app ((@nil Z)) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
|--
  “ (sizeof( "_SM3_CTX" ) = sizeof( "_SM3_CTX" )) ” 
  &&  “ (sm3_digest_input_aligned data_pre datalen_pre ) ” 
  &&  “ (aligned_4 dgst_pre ) ”
  &&  (sm3_ctx_full_shape ( &( "ctx" ) ) )
  **  (store_bytes dgst_pre 32 (sm3_digest_bytes ((app ((@nil Z)) (Message)))) )
  **  (store_sm3_ti )
  **  (store_bytes data_pre datalen_pre Message )
.

Definition sm3_partial_solve_wit_4 := sm3_partial_solve_wit_4_pure -> sm3_partial_solve_wit_4_aux.

Module Type VC_Correct.

Include byte_memory_views_Strategy_Correct.
Include sm3_ctx_views_Strategy_Correct.

Axiom proof_of_sm3_safety_wit_1 : sm3_safety_wit_1.
Axiom proof_of_sm3_safety_wit_2 : sm3_safety_wit_2.
Axiom proof_of_sm3_return_wit_1 : sm3_return_wit_1.
Axiom proof_of_sm3_partial_solve_wit_1 : sm3_partial_solve_wit_1.
Axiom proof_of_sm3_partial_solve_wit_2_pure : sm3_partial_solve_wit_2_pure.
Axiom proof_of_sm3_partial_solve_wit_2 : sm3_partial_solve_wit_2.
Axiom proof_of_sm3_partial_solve_wit_3_pure : sm3_partial_solve_wit_3_pure.
Axiom proof_of_sm3_partial_solve_wit_3 : sm3_partial_solve_wit_3.
Axiom proof_of_sm3_partial_solve_wit_4_pure : sm3_partial_solve_wit_4_pure.
Axiom proof_of_sm3_partial_solve_wit_4 : sm3_partial_solve_wit_4.

End VC_Correct.
