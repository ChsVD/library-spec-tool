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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function double_mod_p -----*)

Definition double_mod_p_safety_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |->_)
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition double_mod_p_safety_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |->_)
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |->_)
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition double_mod_p_safety_wit_4_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_5_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition double_mod_p_safety_wit_6_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition double_mod_p_safety_wit_7_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_8_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_9_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_10_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition double_mod_p_safety_wit_11_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_12_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition double_mod_p_safety_wit_13_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition double_mod_p_safety_wit_14_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_15_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_16_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_17_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition double_mod_p_safety_wit_18_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_19_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition double_mod_p_safety_wit_20_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition double_mod_p_safety_wit_21_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_22_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_23_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_24_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition double_mod_p_safety_wit_25_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 1 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_26_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 1 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition double_mod_p_safety_wit_27_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 1 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_28_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 1 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_29_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "borrow" ) )) # UChar  |->_)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_30_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_31_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_32_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_33_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_34_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_35_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_36_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_37_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_38_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_39_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_40_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_41_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_42_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_43_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_mod_p_safety_wit_44_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_45_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition double_mod_p_safety_wit_46_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_47_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_mod_p_safety_wit_48_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_safety_wit_49_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  ((( &( "borrow" ) )) # UChar  |-> retval_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition double_mod_p_entail_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition double_mod_p_entail_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias < SM2_P_Z)) (PreH2 : (0 <= A_non_alias)) ,
  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition double_mod_p_entail_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition double_mod_p_return_wit_1_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((2 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((2 * A_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD) ” 
  &&  “ ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) = (u256_of_limbs ((unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63))))) ”
  &&  emp
).

Definition double_mod_p_return_wit_1_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (0 <= (Zmod ((2 * A_non_alias )) (SM2_P_Z)))
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) < SM2_P_Z)
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (0 <= (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_4 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD)
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_5 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_6 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD)
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_7 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_8 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD)
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_9 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_10 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD)
.

Definition double_mod_p_return_wit_1_non_alias_split_goal_11 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) = (u256_of_limbs ((unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))))
.

Definition double_mod_p_return_wit_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((2 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((2 * A_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ”
  &&  emp
).

Definition double_mod_p_return_wit_2_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (0 <= (Zmod ((2 * A_non_alias )) (SM2_P_Z)))
.

Definition double_mod_p_return_wit_2_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) < SM2_P_Z)
.

Definition double_mod_p_return_wit_2_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) <> 0)) (PreH2 : (0 <= out_4)) (PreH3 : (out_4 < U64_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH7 : (0 <= out_3)) (PreH8 : (out_3 < U64_MOD)) (PreH9 : (0 <= retval_3)) (PreH10 : (retval_3 <= 1)) (PreH11 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH12 : (0 <= out_2)) (PreH13 : (out_2 < U64_MOD)) (PreH14 : (0 <= retval_2)) (PreH15 : (retval_2 <= 1)) (PreH16 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH17 : (0 <= out)) (PreH18 : (out < U64_MOD)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH22 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH23 : (x3 < U64_MOD)) (PreH24 : (0 <= x3)) (PreH25 : (x2 < U64_MOD)) (PreH26 : (0 <= x2)) (PreH27 : (x1 < U64_MOD)) (PreH28 : (0 <= x1)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (A_non_alias < SM2_P_Z)) (PreH32 : (0 <= A_non_alias)) ,
  ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4)))
.

Definition double_mod_p_return_wit_3_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((2 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((2 * A_non_alias )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ”
  &&  emp
).

Definition double_mod_p_return_wit_3_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  (0 <= (Zmod ((2 * A_non_alias )) (SM2_P_Z)))
.

Definition double_mod_p_return_wit_3_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) < SM2_P_Z)
.

Definition double_mod_p_return_wit_3_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr x3 63)) (8)) = 0)) (PreH3 : (0 <= out_4)) (PreH4 : (out_4 < U64_MOD)) (PreH5 : (0 <= retval_4)) (PreH6 : (retval_4 <= 1)) (PreH7 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH8 : (0 <= out_3)) (PreH9 : (out_3 < U64_MOD)) (PreH10 : (0 <= retval_3)) (PreH11 : (retval_3 <= 1)) (PreH12 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH13 : (0 <= out_2)) (PreH14 : (out_2 < U64_MOD)) (PreH15 : (0 <= retval_2)) (PreH16 : (retval_2 <= 1)) (PreH17 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH18 : (0 <= out)) (PreH19 : (out < U64_MOD)) (PreH20 : (0 <= retval)) (PreH21 : (retval <= 1)) (PreH22 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH23 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH24 : (x3 < U64_MOD)) (PreH25 : (0 <= x3)) (PreH26 : (x2 < U64_MOD)) (PreH27 : (0 <= x2)) (PreH28 : (x1 < U64_MOD)) (PreH29 : (0 <= x1)) (PreH30 : (x0 < U64_MOD)) (PreH31 : (0 <= x0)) (PreH32 : (A_non_alias < SM2_P_Z)) (PreH33 : (0 <= A_non_alias)) ,
  ((Zmod ((2 * A_non_alias )) (SM2_P_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4)))
.

Definition double_mod_p_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 3 0 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition double_mod_p_partial_solve_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 2 0 3 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition double_mod_p_partial_solve_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 1 0 2 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition double_mod_p_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 0 1 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition double_mod_p_partial_solve_wit_5_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 0 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition double_mod_p_partial_solve_wit_6_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH16 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH16 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH16 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ”
.

Definition double_mod_p_partial_solve_wit_6_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (x0 >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH16 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH17 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH18 : (x3 < U64_MOD)) (PreH19 : (0 <= x3)) (PreH20 : (x2 < U64_MOD)) (PreH21 : (0 <= x2)) (PreH22 : (x1 < U64_MOD)) (PreH23 : (0 <= x1)) (PreH24 : (x0 < U64_MOD)) (PreH25 : (0 <= x0)) (PreH26 : (A_non_alias < SM2_P_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_6_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_6_non_alias := double_mod_p_partial_solve_wit_6_non_alias_pure -> double_mod_p_partial_solve_wit_6_non_alias_aux.

Definition double_mod_p_partial_solve_wit_7_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 1 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_8_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH17 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH25 : (x3 < U64_MOD)) (PreH26 : (0 <= x3)) (PreH27 : (x2 < U64_MOD)) (PreH28 : (0 <= x2)) (PreH29 : (x1 < U64_MOD)) (PreH30 : (0 <= x1)) (PreH31 : (x0 < U64_MOD)) (PreH32 : (0 <= x0)) (PreH33 : (A_non_alias < SM2_P_Z)) (PreH34 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH17 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH25 : (x3 < U64_MOD)) (PreH26 : (0 <= x3)) (PreH27 : (x2 < U64_MOD)) (PreH28 : (0 <= x2)) (PreH29 : (x1 < U64_MOD)) (PreH30 : (0 <= x1)) (PreH31 : (x0 < U64_MOD)) (PreH32 : (0 <= x0)) (PreH33 : (A_non_alias < SM2_P_Z)) (PreH34 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH17 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH25 : (x3 < U64_MOD)) (PreH26 : (0 <= x3)) (PreH27 : (x2 < U64_MOD)) (PreH28 : (0 <= x2)) (PreH29 : (x1 < U64_MOD)) (PreH30 : (0 <= x1)) (PreH31 : (x0 < U64_MOD)) (PreH32 : (0 <= x0)) (PreH33 : (A_non_alias < SM2_P_Z)) (PreH34 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ”
.

Definition double_mod_p_partial_solve_wit_8_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (x0 >= 0)) (PreH11 : (x1 >= 0)) (PreH12 : (x2 >= 0)) (PreH13 : (x3 >= 0)) (PreH14 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH17 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH18 : (out >= 0)) (PreH19 : (0 <= out)) (PreH20 : (out < U64_MOD)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH24 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH25 : (x3 < U64_MOD)) (PreH26 : (0 <= x3)) (PreH27 : (x2 < U64_MOD)) (PreH28 : (0 <= x2)) (PreH29 : (x1 < U64_MOD)) (PreH30 : (0 <= x1)) (PreH31 : (x0 < U64_MOD)) (PreH32 : (0 <= x0)) (PreH33 : (A_non_alias < SM2_P_Z)) (PreH34 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_8_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_8_non_alias := double_mod_p_partial_solve_wit_8_non_alias_pure -> double_mod_p_partial_solve_wit_8_non_alias_aux.

Definition double_mod_p_partial_solve_wit_9_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 2 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_10_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH18 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (A_non_alias < SM2_P_Z)) (PreH41 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH18 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (A_non_alias < SM2_P_Z)) (PreH41 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH18 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (A_non_alias < SM2_P_Z)) (PreH41 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ”
.

Definition double_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (x0 >= 0)) (PreH12 : (x1 >= 0)) (PreH13 : (x2 >= 0)) (PreH14 : (x3 >= 0)) (PreH15 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH18 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH19 : (out >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH31 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (A_non_alias < SM2_P_Z)) (PreH41 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_10_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_10_non_alias := double_mod_p_partial_solve_wit_10_non_alias_pure -> double_mod_p_partial_solve_wit_10_non_alias_aux.

Definition double_mod_p_partial_solve_wit_11_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 3 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_12_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63))) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH18 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH19 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH39 : (x3 < U64_MOD)) (PreH40 : (0 <= x3)) (PreH41 : (x2 < U64_MOD)) (PreH42 : (0 <= x2)) (PreH43 : (x1 < U64_MOD)) (PreH44 : (0 <= x1)) (PreH45 : (x0 < U64_MOD)) (PreH46 : (0 <= x0)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH18 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH19 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH39 : (x3 < U64_MOD)) (PreH40 : (0 <= x3)) (PreH41 : (x2 < U64_MOD)) (PreH42 : (0 <= x2)) (PreH43 : (x1 < U64_MOD)) (PreH44 : (0 <= x1)) (PreH45 : (x0 < U64_MOD)) (PreH46 : (0 <= x0)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH18 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH19 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH39 : (x3 < U64_MOD)) (PreH40 : (0 <= x3)) (PreH41 : (x2 < U64_MOD)) (PreH42 : (0 <= x2)) (PreH43 : (x1 < U64_MOD)) (PreH44 : (0 <= x1)) (PreH45 : (x0 < U64_MOD)) (PreH46 : (0 <= x0)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ”
.

Definition double_mod_p_partial_solve_wit_12_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) <= UINT64_MAX)) (PreH6 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) <= UINT64_MAX)) (PreH7 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) <= UINT64_MAX)) (PreH8 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (x0 >= 0)) (PreH13 : (x1 >= 0)) (PreH14 : (x2 >= 0)) (PreH15 : (x3 >= 0)) (PreH16 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) >= 0)) (PreH17 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) >= 0)) (PreH18 : ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) >= 0)) (PreH19 : ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) >= 0)) (PreH20 : (out >= 0)) (PreH21 : (out_2 >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (0 <= out_3)) (PreH24 : (out_3 < U64_MOD)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH28 : (0 <= out_2)) (PreH29 : (out_2 < U64_MOD)) (PreH30 : (0 <= retval_3)) (PreH31 : (retval_3 <= 1)) (PreH32 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH33 : (0 <= out)) (PreH34 : (out < U64_MOD)) (PreH35 : (0 <= retval_2)) (PreH36 : (retval_2 <= 1)) (PreH37 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH38 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH39 : (x3 < U64_MOD)) (PreH40 : (0 <= x3)) (PreH41 : (x2 < U64_MOD)) (PreH42 : (0 <= x2)) (PreH43 : (x1 < U64_MOD)) (PreH44 : (0 <= x1)) (PreH45 : (x0 < U64_MOD)) (PreH46 : (0 <= x0)) (PreH47 : (A_non_alias < SM2_P_Z)) (PreH48 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  ((( &( "overflow" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition double_mod_p_partial_solve_wit_12_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63))) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition double_mod_p_partial_solve_wit_12_non_alias := double_mod_p_partial_solve_wit_12_non_alias_pure -> double_mod_p_partial_solve_wit_12_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_double_mod_p_safety_wit_1_non_alias : double_mod_p_safety_wit_1_non_alias.
Axiom proof_of_double_mod_p_safety_wit_2_non_alias : double_mod_p_safety_wit_2_non_alias.
Axiom proof_of_double_mod_p_safety_wit_3_non_alias : double_mod_p_safety_wit_3_non_alias.
Axiom proof_of_double_mod_p_safety_wit_4_non_alias : double_mod_p_safety_wit_4_non_alias.
Axiom proof_of_double_mod_p_safety_wit_5_non_alias : double_mod_p_safety_wit_5_non_alias.
Axiom proof_of_double_mod_p_safety_wit_6_non_alias : double_mod_p_safety_wit_6_non_alias.
Axiom proof_of_double_mod_p_safety_wit_7_non_alias : double_mod_p_safety_wit_7_non_alias.
Axiom proof_of_double_mod_p_safety_wit_8_non_alias : double_mod_p_safety_wit_8_non_alias.
Axiom proof_of_double_mod_p_safety_wit_9_non_alias : double_mod_p_safety_wit_9_non_alias.
Axiom proof_of_double_mod_p_safety_wit_10_non_alias : double_mod_p_safety_wit_10_non_alias.
Axiom proof_of_double_mod_p_safety_wit_11_non_alias : double_mod_p_safety_wit_11_non_alias.
Axiom proof_of_double_mod_p_safety_wit_12_non_alias : double_mod_p_safety_wit_12_non_alias.
Axiom proof_of_double_mod_p_safety_wit_13_non_alias : double_mod_p_safety_wit_13_non_alias.
Axiom proof_of_double_mod_p_safety_wit_14_non_alias : double_mod_p_safety_wit_14_non_alias.
Axiom proof_of_double_mod_p_safety_wit_15_non_alias : double_mod_p_safety_wit_15_non_alias.
Axiom proof_of_double_mod_p_safety_wit_16_non_alias : double_mod_p_safety_wit_16_non_alias.
Axiom proof_of_double_mod_p_safety_wit_17_non_alias : double_mod_p_safety_wit_17_non_alias.
Axiom proof_of_double_mod_p_safety_wit_18_non_alias : double_mod_p_safety_wit_18_non_alias.
Axiom proof_of_double_mod_p_safety_wit_19_non_alias : double_mod_p_safety_wit_19_non_alias.
Axiom proof_of_double_mod_p_safety_wit_20_non_alias : double_mod_p_safety_wit_20_non_alias.
Axiom proof_of_double_mod_p_safety_wit_21_non_alias : double_mod_p_safety_wit_21_non_alias.
Axiom proof_of_double_mod_p_safety_wit_22_non_alias : double_mod_p_safety_wit_22_non_alias.
Axiom proof_of_double_mod_p_safety_wit_23_non_alias : double_mod_p_safety_wit_23_non_alias.
Axiom proof_of_double_mod_p_safety_wit_24_non_alias : double_mod_p_safety_wit_24_non_alias.
Axiom proof_of_double_mod_p_safety_wit_25_non_alias : double_mod_p_safety_wit_25_non_alias.
Axiom proof_of_double_mod_p_safety_wit_26_non_alias : double_mod_p_safety_wit_26_non_alias.
Axiom proof_of_double_mod_p_safety_wit_27_non_alias : double_mod_p_safety_wit_27_non_alias.
Axiom proof_of_double_mod_p_safety_wit_28_non_alias : double_mod_p_safety_wit_28_non_alias.
Axiom proof_of_double_mod_p_safety_wit_29_non_alias : double_mod_p_safety_wit_29_non_alias.
Axiom proof_of_double_mod_p_safety_wit_30_non_alias : double_mod_p_safety_wit_30_non_alias.
Axiom proof_of_double_mod_p_safety_wit_31_non_alias : double_mod_p_safety_wit_31_non_alias.
Axiom proof_of_double_mod_p_safety_wit_32_non_alias : double_mod_p_safety_wit_32_non_alias.
Axiom proof_of_double_mod_p_safety_wit_33_non_alias : double_mod_p_safety_wit_33_non_alias.
Axiom proof_of_double_mod_p_safety_wit_34_non_alias : double_mod_p_safety_wit_34_non_alias.
Axiom proof_of_double_mod_p_safety_wit_35_non_alias : double_mod_p_safety_wit_35_non_alias.
Axiom proof_of_double_mod_p_safety_wit_36_non_alias : double_mod_p_safety_wit_36_non_alias.
Axiom proof_of_double_mod_p_safety_wit_37_non_alias : double_mod_p_safety_wit_37_non_alias.
Axiom proof_of_double_mod_p_safety_wit_38_non_alias : double_mod_p_safety_wit_38_non_alias.
Axiom proof_of_double_mod_p_safety_wit_39_non_alias : double_mod_p_safety_wit_39_non_alias.
Axiom proof_of_double_mod_p_safety_wit_40_non_alias : double_mod_p_safety_wit_40_non_alias.
Axiom proof_of_double_mod_p_safety_wit_41_non_alias : double_mod_p_safety_wit_41_non_alias.
Axiom proof_of_double_mod_p_safety_wit_42_non_alias : double_mod_p_safety_wit_42_non_alias.
Axiom proof_of_double_mod_p_safety_wit_43_non_alias : double_mod_p_safety_wit_43_non_alias.
Axiom proof_of_double_mod_p_safety_wit_44_non_alias : double_mod_p_safety_wit_44_non_alias.
Axiom proof_of_double_mod_p_safety_wit_45_non_alias : double_mod_p_safety_wit_45_non_alias.
Axiom proof_of_double_mod_p_safety_wit_46_non_alias : double_mod_p_safety_wit_46_non_alias.
Axiom proof_of_double_mod_p_safety_wit_47_non_alias : double_mod_p_safety_wit_47_non_alias.
Axiom proof_of_double_mod_p_safety_wit_48_non_alias : double_mod_p_safety_wit_48_non_alias.
Axiom proof_of_double_mod_p_safety_wit_49_non_alias : double_mod_p_safety_wit_49_non_alias.
Axiom proof_of_double_mod_p_entail_wit_1_non_alias : double_mod_p_entail_wit_1_non_alias.
Axiom proof_of_double_mod_p_entail_wit_2_non_alias : double_mod_p_entail_wit_2_non_alias.
Axiom proof_of_double_mod_p_entail_wit_3_non_alias : double_mod_p_entail_wit_3_non_alias.
Axiom proof_of_double_mod_p_return_wit_1_non_alias : double_mod_p_return_wit_1_non_alias.
Axiom proof_of_double_mod_p_return_wit_2_non_alias : double_mod_p_return_wit_2_non_alias.
Axiom proof_of_double_mod_p_return_wit_3_non_alias : double_mod_p_return_wit_3_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_1_non_alias : double_mod_p_partial_solve_wit_1_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_2_non_alias : double_mod_p_partial_solve_wit_2_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_3_non_alias : double_mod_p_partial_solve_wit_3_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_4_non_alias : double_mod_p_partial_solve_wit_4_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_5_non_alias : double_mod_p_partial_solve_wit_5_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_6_non_alias_pure : double_mod_p_partial_solve_wit_6_non_alias_pure.
Axiom proof_of_double_mod_p_partial_solve_wit_6_non_alias : double_mod_p_partial_solve_wit_6_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_7_non_alias : double_mod_p_partial_solve_wit_7_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_8_non_alias_pure : double_mod_p_partial_solve_wit_8_non_alias_pure.
Axiom proof_of_double_mod_p_partial_solve_wit_8_non_alias : double_mod_p_partial_solve_wit_8_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_9_non_alias : double_mod_p_partial_solve_wit_9_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_10_non_alias_pure : double_mod_p_partial_solve_wit_10_non_alias_pure.
Axiom proof_of_double_mod_p_partial_solve_wit_10_non_alias : double_mod_p_partial_solve_wit_10_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_11_non_alias : double_mod_p_partial_solve_wit_11_non_alias.
Axiom proof_of_double_mod_p_partial_solve_wit_12_non_alias_pure : double_mod_p_partial_solve_wit_12_non_alias_pure.
Axiom proof_of_double_mod_p_partial_solve_wit_12_non_alias : double_mod_p_partial_solve_wit_12_non_alias.

End VC_Correct.
