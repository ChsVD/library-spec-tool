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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import add_mod_n_def.
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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function add_mod_n -----*)

Definition add_mod_n_safety_wit_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_2_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_3_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_4_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_5_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_6_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_7_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_8_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_9_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_N_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_N_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_10_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_N_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_N_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_11_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_N_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_N_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_12_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_N_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_N_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_13_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_N_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_N_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_14_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_N_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_N_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_15_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_N_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_N_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_16_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_N_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_N_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_17_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_N_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_N_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_18_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_N_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_19_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_N_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_20_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_N_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_21_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_N_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_N_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_22_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_N_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_N_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_23_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_N_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_N_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_24_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_N_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_N_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_25_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_N_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_N_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_26_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_N_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_N_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_27_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  ((( &( "borrow" ) )) # UChar  |->_)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_28_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  ((( &( "borrow" ) )) # UChar  |->_)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_29_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_30_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_31_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_32_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_33_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_34_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_35_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_r_eq_b < SM2_N_Z)) (PreH45 : (0 <= B_r_eq_b)) (PreH46 : (A_r_eq_b < SM2_N_Z)) (PreH47 : (0 <= A_r_eq_b)) (PreH48 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> retval_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_36_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_r_eq_b < SM2_N_Z)) (PreH45 : (0 <= B_r_eq_b)) (PreH46 : (A_r_eq_b < SM2_N_Z)) (PreH47 : (0 <= A_r_eq_b)) (PreH48 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> retval_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_37_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_r_eq_b < SM2_N_Z)) (PreH45 : (0 <= B_r_eq_b)) (PreH46 : (A_r_eq_b < SM2_N_Z)) (PreH47 : (0 <= A_r_eq_b)) (PreH48 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_38_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_non_alias < SM2_N_Z)) (PreH45 : (0 <= B_non_alias)) (PreH46 : (A_non_alias < SM2_N_Z)) (PreH47 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> retval_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_39_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_non_alias < SM2_N_Z)) (PreH45 : (0 <= B_non_alias)) (PreH46 : (A_non_alias < SM2_N_Z)) (PreH47 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> retval_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_40_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_non_alias < SM2_N_Z)) (PreH45 : (0 <= B_non_alias)) (PreH46 : (A_non_alias < SM2_N_Z)) (PreH47 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_41_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_r_eq_b < SM2_N_Z)) (PreH50 : (0 <= B_r_eq_b)) (PreH51 : (A_r_eq_b < SM2_N_Z)) (PreH52 : (0 <= A_r_eq_b)) (PreH53 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_6)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_42_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_r_eq_b < SM2_N_Z)) (PreH50 : (0 <= B_r_eq_b)) (PreH51 : (A_r_eq_b < SM2_N_Z)) (PreH52 : (0 <= A_r_eq_b)) (PreH53 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_6)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_43_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_r_eq_b < SM2_N_Z)) (PreH50 : (0 <= B_r_eq_b)) (PreH51 : (A_r_eq_b < SM2_N_Z)) (PreH52 : (0 <= A_r_eq_b)) (PreH53 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_6)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_44_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_N_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_N_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_6)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_45_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_N_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_N_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_6)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_46_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_N_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_N_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_6)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_47_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_r_eq_b < SM2_N_Z)) (PreH55 : (0 <= B_r_eq_b)) (PreH56 : (A_r_eq_b < SM2_N_Z)) (PreH57 : (0 <= A_r_eq_b)) (PreH58 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_7)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_48_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_r_eq_b < SM2_N_Z)) (PreH55 : (0 <= B_r_eq_b)) (PreH56 : (A_r_eq_b < SM2_N_Z)) (PreH57 : (0 <= A_r_eq_b)) (PreH58 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_7)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_49_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_r_eq_b < SM2_N_Z)) (PreH55 : (0 <= B_r_eq_b)) (PreH56 : (A_r_eq_b < SM2_N_Z)) (PreH57 : (0 <= A_r_eq_b)) (PreH58 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_7)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_50_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_non_alias < SM2_N_Z)) (PreH55 : (0 <= B_non_alias)) (PreH56 : (A_non_alias < SM2_N_Z)) (PreH57 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_7)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_51_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_non_alias < SM2_N_Z)) (PreH55 : (0 <= B_non_alias)) (PreH56 : (A_non_alias < SM2_N_Z)) (PreH57 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_7)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_52_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_non_alias < SM2_N_Z)) (PreH55 : (0 <= B_non_alias)) (PreH56 : (A_non_alias < SM2_N_Z)) (PreH57 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_7)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_53_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_54_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_55_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_56_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_mod_n_safety_wit_57_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_58_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_59_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_60_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition add_mod_n_safety_wit_61_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_62_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_63_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_64_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition add_mod_n_safety_wit_65_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_66_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_67_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_safety_wit_68_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition add_mod_n_entail_wit_1_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = b_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn a_pre A_r_eq_b )
  **  (store_fn b_pre B_r_eq_b )
  **  (store_sm2_n )
|--
  (“ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n ))
  ||
  (“ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n ))
.

Definition add_mod_n_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn a_pre A_non_alias )
  **  (store_fn b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
|--
  (“ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n ))
  ||
  (“ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n ))
.

Definition add_mod_n_entail_wit_2_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (B_r_eq_b < SM2_N_Z)) (PreH2 : (0 <= B_r_eq_b)) (PreH3 : (A_r_eq_b < SM2_N_Z)) (PreH4 : (0 <= A_r_eq_b)) (PreH5 : (result_pre = b_pre)) ,
  (store_u256 b_pre B_r_eq_b )
  **  (store_u256 a_pre A_r_eq_b )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n ))
.

Definition add_mod_n_entail_wit_2_2_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (B_non_alias < SM2_N_Z)) (PreH2 : (0 <= B_non_alias)) (PreH3 : (A_non_alias < SM2_N_Z)) (PreH4 : (0 <= A_non_alias)) ,
  (store_u256 b_pre B_non_alias )
  **  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n ))
.

Definition add_mod_n_entail_wit_3_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
|--
  (“ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (B_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition add_mod_n_entail_wit_3_2_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (A_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (B_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition add_mod_n_entail_wit_4_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_entail_wit_5_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition add_mod_n_entail_wit_6_1_non_alias := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (limbs: (@list Z)) ,
  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_non_alias + B_non_alias )) (U256_MOD))) ”
  &&  (store_fn a_pre A_non_alias )
  **  (store_fn b_pre B_non_alias )
  **  (store_fn result_pre (Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) )
  **  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
  **  (store_sm2_n )
  **  ((( &( "carry" ) )) # UChar  |->_)
  **  ((( &( "borrow" ) )) # UChar  |->_)
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (out <= UINT64_MAX)) (PreH2 : (out_2 <= UINT64_MAX)) (PreH3 : (out_3 <= UINT64_MAX)) (PreH4 : (out_4 <= UINT64_MAX)) (PreH5 : (out >= 0)) (PreH6 : (out_2 >= 0)) (PreH7 : (out_3 >= 0)) (PreH8 : (out_4 >= 0)) (PreH9 : ((Z.lor retval_4 retval_8) = 0)) (PreH10 : (0 <= out_8)) (PreH11 : (out_8 < U64_MOD)) (PreH12 : (0 <= retval_8)) (PreH13 : (retval_8 <= 1)) (PreH14 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH15 : (0 <= out_7)) (PreH16 : (out_7 < U64_MOD)) (PreH17 : (0 <= retval_7)) (PreH18 : (retval_7 <= 1)) (PreH19 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH20 : (0 <= out_6)) (PreH21 : (out_6 < U64_MOD)) (PreH22 : (0 <= retval_6)) (PreH23 : (retval_6 <= 1)) (PreH24 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval_5)) (PreH28 : (retval_5 <= 1)) (PreH29 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_4)) (PreH33 : (retval_4 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_3)) (PreH38 : (retval_3 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH40 : (0 <= out_2)) (PreH41 : (out_2 < U64_MOD)) (PreH42 : (0 <= retval_2)) (PreH43 : (retval_2 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH45 : (0 <= out)) (PreH46 : (out < U64_MOD)) (PreH47 : (0 <= retval)) (PreH48 : (retval <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH50 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_non_alias < SM2_N_Z)) (PreH69 : (0 <= B_non_alias)) (PreH70 : (A_non_alias < SM2_N_Z)) (PreH71 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
|--
  EX (limbs: (@list Z)) ,
  “ ((Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= out) ” 
  &&  “ ((Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z))) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_non_alias + B_non_alias )) (U256_MOD))) ”
  &&  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
).

Definition add_mod_n_entail_wit_6_2_non_alias := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) <> 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_non_alias < SM2_N_Z)) (PreH61 : (0 <= B_non_alias)) (PreH62 : (A_non_alias < SM2_N_Z)) (PreH63 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (limbs: (@list Z)) ,
  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_non_alias + B_non_alias )) (U256_MOD))) ”
  &&  (store_fn a_pre A_non_alias )
  **  (store_fn b_pre B_non_alias )
  **  (store_fn result_pre (Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) )
  **  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
  **  (store_sm2_n )
  **  ((( &( "carry" ) )) # UChar  |->_)
  **  ((( &( "borrow" ) )) # UChar  |->_)
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (out <= UINT64_MAX)) (PreH2 : (out_2 <= UINT64_MAX)) (PreH3 : (out_3 <= UINT64_MAX)) (PreH4 : (out_4 <= UINT64_MAX)) (PreH5 : (out >= 0)) (PreH6 : (out_2 >= 0)) (PreH7 : (out_3 >= 0)) (PreH8 : (out_4 >= 0)) (PreH9 : ((Z.lor retval_4 retval_8) <> 0)) (PreH10 : (0 <= out_8)) (PreH11 : (out_8 < U64_MOD)) (PreH12 : (0 <= retval_8)) (PreH13 : (retval_8 <= 1)) (PreH14 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH15 : (0 <= out_7)) (PreH16 : (out_7 < U64_MOD)) (PreH17 : (0 <= retval_7)) (PreH18 : (retval_7 <= 1)) (PreH19 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH20 : (0 <= out_6)) (PreH21 : (out_6 < U64_MOD)) (PreH22 : (0 <= retval_6)) (PreH23 : (retval_6 <= 1)) (PreH24 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval_5)) (PreH28 : (retval_5 <= 1)) (PreH29 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_4)) (PreH33 : (retval_4 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_3)) (PreH38 : (retval_3 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH40 : (0 <= out_2)) (PreH41 : (out_2 < U64_MOD)) (PreH42 : (0 <= retval_2)) (PreH43 : (retval_2 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH45 : (0 <= out)) (PreH46 : (out < U64_MOD)) (PreH47 : (0 <= retval)) (PreH48 : (retval <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH50 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_non_alias < SM2_N_Z)) (PreH69 : (0 <= B_non_alias)) (PreH70 : (A_non_alias < SM2_N_Z)) (PreH71 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
|--
  EX (limbs: (@list Z)) ,
  “ ((Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8))) ” 
  &&  “ (out_8 < U64_MOD) ” 
  &&  “ (0 <= out_8) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ ((Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z))) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_non_alias + B_non_alias )) (U256_MOD))) ”
  &&  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
).

Definition add_mod_n_entail_wit_7_1_r_eq_b := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) = 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (limbs: (@list Z)) ,
  “ (result_pre = b_pre) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_r_eq_b + B_r_eq_b )) (U256_MOD))) ”
  &&  (store_fn a_pre A_r_eq_b )
  **  (store_fn result_pre (Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) )
  **  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
  **  (store_sm2_n )
  **  ((( &( "carry" ) )) # UChar  |->_)
  **  ((( &( "borrow" ) )) # UChar  |->_)
) \/
(
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (out <= UINT64_MAX)) (PreH2 : (out_2 <= UINT64_MAX)) (PreH3 : (out_3 <= UINT64_MAX)) (PreH4 : (out_4 <= UINT64_MAX)) (PreH5 : (out >= 0)) (PreH6 : (out_2 >= 0)) (PreH7 : (out_3 >= 0)) (PreH8 : (out_4 >= 0)) (PreH9 : ((Z.lor retval_4 retval_8) = 0)) (PreH10 : (0 <= out_8)) (PreH11 : (out_8 < U64_MOD)) (PreH12 : (0 <= retval_8)) (PreH13 : (retval_8 <= 1)) (PreH14 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH15 : (0 <= out_7)) (PreH16 : (out_7 < U64_MOD)) (PreH17 : (0 <= retval_7)) (PreH18 : (retval_7 <= 1)) (PreH19 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH20 : (0 <= out_6)) (PreH21 : (out_6 < U64_MOD)) (PreH22 : (0 <= retval_6)) (PreH23 : (retval_6 <= 1)) (PreH24 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval_5)) (PreH28 : (retval_5 <= 1)) (PreH29 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_4)) (PreH33 : (retval_4 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_3)) (PreH38 : (retval_3 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH40 : (0 <= out_2)) (PreH41 : (out_2 < U64_MOD)) (PreH42 : (0 <= retval_2)) (PreH43 : (retval_2 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH45 : (0 <= out)) (PreH46 : (out < U64_MOD)) (PreH47 : (0 <= retval)) (PreH48 : (retval <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH50 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_r_eq_b < SM2_N_Z)) (PreH69 : (0 <= B_r_eq_b)) (PreH70 : (A_r_eq_b < SM2_N_Z)) (PreH71 : (0 <= A_r_eq_b)) (PreH72 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
|--
  EX (limbs: (@list Z)) ,
  “ ((Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) = (u256_of_limbs (out) (out_2) (out_3) (out_4))) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= out) ” 
  &&  “ ((Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z))) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_r_eq_b + B_r_eq_b )) (U256_MOD))) ”
  &&  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
).

Definition add_mod_n_entail_wit_7_2_r_eq_b := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : ((Z.lor retval_4 retval_8) <> 0)) (PreH2 : (0 <= out_8)) (PreH3 : (out_8 < U64_MOD)) (PreH4 : (0 <= retval_8)) (PreH5 : (retval_8 <= 1)) (PreH6 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH7 : (0 <= out_7)) (PreH8 : (out_7 < U64_MOD)) (PreH9 : (0 <= retval_7)) (PreH10 : (retval_7 <= 1)) (PreH11 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH12 : (0 <= out_6)) (PreH13 : (out_6 < U64_MOD)) (PreH14 : (0 <= retval_6)) (PreH15 : (retval_6 <= 1)) (PreH16 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH17 : (0 <= out_5)) (PreH18 : (out_5 < U64_MOD)) (PreH19 : (0 <= retval_5)) (PreH20 : (retval_5 <= 1)) (PreH21 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH22 : (0 <= out_4)) (PreH23 : (out_4 < U64_MOD)) (PreH24 : (0 <= retval_4)) (PreH25 : (retval_4 <= 1)) (PreH26 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH27 : (0 <= out_3)) (PreH28 : (out_3 < U64_MOD)) (PreH29 : (0 <= retval_3)) (PreH30 : (retval_3 <= 1)) (PreH31 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH32 : (0 <= out_2)) (PreH33 : (out_2 < U64_MOD)) (PreH34 : (0 <= retval_2)) (PreH35 : (retval_2 <= 1)) (PreH36 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH37 : (0 <= out)) (PreH38 : (out < U64_MOD)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH42 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH43 : (x3_2 < U64_MOD)) (PreH44 : (0 <= x3_2)) (PreH45 : (x2_2 < U64_MOD)) (PreH46 : (0 <= x2_2)) (PreH47 : (x1_2 < U64_MOD)) (PreH48 : (0 <= x1_2)) (PreH49 : (x0_2 < U64_MOD)) (PreH50 : (0 <= x0_2)) (PreH51 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH52 : (x3 < U64_MOD)) (PreH53 : (0 <= x3)) (PreH54 : (x2 < U64_MOD)) (PreH55 : (0 <= x2)) (PreH56 : (x1 < U64_MOD)) (PreH57 : (0 <= x1)) (PreH58 : (x0 < U64_MOD)) (PreH59 : (0 <= x0)) (PreH60 : (B_r_eq_b < SM2_N_Z)) (PreH61 : (0 <= B_r_eq_b)) (PreH62 : (A_r_eq_b < SM2_N_Z)) (PreH63 : (0 <= A_r_eq_b)) (PreH64 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_8)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval_8)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  EX (limbs: (@list Z)) ,
  “ (result_pre = b_pre) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_r_eq_b + B_r_eq_b )) (U256_MOD))) ”
  &&  (store_fn a_pre A_r_eq_b )
  **  (store_fn result_pre (Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) )
  **  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
  **  (store_sm2_n )
  **  ((( &( "carry" ) )) # UChar  |->_)
  **  ((( &( "borrow" ) )) # UChar  |->_)
) \/
(
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (out_8: Z) (retval_8: Z) (PreH1 : (out <= UINT64_MAX)) (PreH2 : (out_2 <= UINT64_MAX)) (PreH3 : (out_3 <= UINT64_MAX)) (PreH4 : (out_4 <= UINT64_MAX)) (PreH5 : (out >= 0)) (PreH6 : (out_2 >= 0)) (PreH7 : (out_3 >= 0)) (PreH8 : (out_4 >= 0)) (PreH9 : ((Z.lor retval_4 retval_8) <> 0)) (PreH10 : (0 <= out_8)) (PreH11 : (out_8 < U64_MOD)) (PreH12 : (0 <= retval_8)) (PreH13 : (retval_8 <= 1)) (PreH14 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_8 + (retval_8 * U64_MOD ) ))) (PreH15 : (0 <= out_7)) (PreH16 : (out_7 < U64_MOD)) (PreH17 : (0 <= retval_7)) (PreH18 : (retval_7 <= 1)) (PreH19 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH20 : (0 <= out_6)) (PreH21 : (out_6 < U64_MOD)) (PreH22 : (0 <= retval_6)) (PreH23 : (retval_6 <= 1)) (PreH24 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval_5)) (PreH28 : (retval_5 <= 1)) (PreH29 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_4)) (PreH33 : (retval_4 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_3)) (PreH38 : (retval_3 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH40 : (0 <= out_2)) (PreH41 : (out_2 < U64_MOD)) (PreH42 : (0 <= retval_2)) (PreH43 : (retval_2 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH45 : (0 <= out)) (PreH46 : (out < U64_MOD)) (PreH47 : (0 <= retval)) (PreH48 : (retval <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH50 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_r_eq_b < SM2_N_Z)) (PreH69 : (0 <= B_r_eq_b)) (PreH70 : (A_r_eq_b < SM2_N_Z)) (PreH71 : (0 <= A_r_eq_b)) (PreH72 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
|--
  EX (limbs: (@list Z)) ,
  “ ((Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) = (u256_of_limbs (out_5) (out_6) (out_7) (out_8))) ” 
  &&  “ (out_8 < U64_MOD) ” 
  &&  “ (0 <= out_8) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ ((Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z))) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ” 
  &&  “ ((Zlength (limbs)) = 4) ” 
  &&  “ (u64_list_bounded limbs ) ” 
  &&  “ ((u64_list_value (limbs)) = (Zmod ((A_r_eq_b + B_r_eq_b )) (U256_MOD))) ”
  &&  (StructPredu32 ( &( "tmp" ) ) (make_record_u32 (limbs)) )
).

Definition add_mod_n_return_wit_1_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (limbs: (@list Z)) (PreH1 : (result_pre = b_pre)) (PreH2 : ((Zlength (limbs)) = 4)) (PreH3 : (u64_list_bounded limbs )) (PreH4 : ((u64_list_value (limbs)) = (Zmod ((A_r_eq_b + B_r_eq_b )) (U256_MOD)))) ,
  (store_fn a_pre A_r_eq_b )
  **  (store_fn result_pre (Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) )
  **  (store_sm2_n )
|--
  “ (result_pre = b_pre) ”
  &&  (store_fn a_pre A_r_eq_b )
  **  (store_fn result_pre (Zmod ((A_r_eq_b + B_r_eq_b )) (SM2_N_Z)) )
  **  (store_sm2_n )
.

Definition add_mod_n_return_wit_2_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (limbs: (@list Z)) (PreH1 : ((Zlength (limbs)) = 4)) (PreH2 : (u64_list_bounded limbs )) (PreH3 : ((u64_list_value (limbs)) = (Zmod ((A_non_alias + B_non_alias )) (U256_MOD)))) ,
  (store_fn a_pre A_non_alias )
  **  (store_fn b_pre B_non_alias )
  **  (store_fn result_pre (Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) )
  **  (store_sm2_n )
|--
  (store_fn a_pre A_non_alias )
  **  (store_fn b_pre B_non_alias )
  **  (store_fn result_pre (Zmod ((A_non_alias + B_non_alias )) (SM2_N_Z)) )
  **  (store_sm2_n )
.

Definition add_mod_n_partial_solve_wit_1_r_eq_b_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_1_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_r_eq_b < SM2_N_Z)) (PreH20 : (0 <= B_r_eq_b)) (PreH21 : (A_r_eq_b < SM2_N_Z)) (PreH22 : (0 <= A_r_eq_b)) (PreH23 : (result_pre = b_pre)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_1_r_eq_b := add_mod_n_partial_solve_wit_1_r_eq_b_pure -> add_mod_n_partial_solve_wit_1_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_2_non_alias_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_2_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (B_non_alias < SM2_N_Z)) (PreH20 : (0 <= B_non_alias)) (PreH21 : (A_non_alias < SM2_N_Z)) (PreH22 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition add_mod_n_partial_solve_wit_2_non_alias := add_mod_n_partial_solve_wit_2_non_alias_pure -> add_mod_n_partial_solve_wit_2_non_alias_aux.

Definition add_mod_n_partial_solve_wit_3_r_eq_b_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_N_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_N_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_3_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_r_eq_b < SM2_N_Z)) (PreH25 : (0 <= B_r_eq_b)) (PreH26 : (A_r_eq_b < SM2_N_Z)) (PreH27 : (0 <= A_r_eq_b)) (PreH28 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_3_r_eq_b := add_mod_n_partial_solve_wit_3_r_eq_b_pure -> add_mod_n_partial_solve_wit_3_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_4_non_alias_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_N_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_N_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_4_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH7 : (x3_2 < U64_MOD)) (PreH8 : (0 <= x3_2)) (PreH9 : (x2_2 < U64_MOD)) (PreH10 : (0 <= x2_2)) (PreH11 : (x1_2 < U64_MOD)) (PreH12 : (0 <= x1_2)) (PreH13 : (x0_2 < U64_MOD)) (PreH14 : (0 <= x0_2)) (PreH15 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH16 : (x3 < U64_MOD)) (PreH17 : (0 <= x3)) (PreH18 : (x2 < U64_MOD)) (PreH19 : (0 <= x2)) (PreH20 : (x1 < U64_MOD)) (PreH21 : (0 <= x1)) (PreH22 : (x0 < U64_MOD)) (PreH23 : (0 <= x0)) (PreH24 : (B_non_alias < SM2_N_Z)) (PreH25 : (0 <= B_non_alias)) (PreH26 : (A_non_alias < SM2_N_Z)) (PreH27 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition add_mod_n_partial_solve_wit_4_non_alias := add_mod_n_partial_solve_wit_4_non_alias_pure -> add_mod_n_partial_solve_wit_4_non_alias_aux.

Definition add_mod_n_partial_solve_wit_5_r_eq_b_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_N_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_N_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_5_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_r_eq_b < SM2_N_Z)) (PreH30 : (0 <= B_r_eq_b)) (PreH31 : (A_r_eq_b < SM2_N_Z)) (PreH32 : (0 <= A_r_eq_b)) (PreH33 : (result_pre = b_pre)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_5_r_eq_b := add_mod_n_partial_solve_wit_5_r_eq_b_pure -> add_mod_n_partial_solve_wit_5_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_6_non_alias_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_N_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_6_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH12 : (x3_2 < U64_MOD)) (PreH13 : (0 <= x3_2)) (PreH14 : (x2_2 < U64_MOD)) (PreH15 : (0 <= x2_2)) (PreH16 : (x1_2 < U64_MOD)) (PreH17 : (0 <= x1_2)) (PreH18 : (x0_2 < U64_MOD)) (PreH19 : (0 <= x0_2)) (PreH20 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH21 : (x3 < U64_MOD)) (PreH22 : (0 <= x3)) (PreH23 : (x2 < U64_MOD)) (PreH24 : (0 <= x2)) (PreH25 : (x1 < U64_MOD)) (PreH26 : (0 <= x1)) (PreH27 : (x0 < U64_MOD)) (PreH28 : (0 <= x0)) (PreH29 : (B_non_alias < SM2_N_Z)) (PreH30 : (0 <= B_non_alias)) (PreH31 : (A_non_alias < SM2_N_Z)) (PreH32 : (0 <= A_non_alias)) ,
  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition add_mod_n_partial_solve_wit_6_non_alias := add_mod_n_partial_solve_wit_6_non_alias_pure -> add_mod_n_partial_solve_wit_6_non_alias_aux.

Definition add_mod_n_partial_solve_wit_7_r_eq_b_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_N_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_N_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_7_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_r_eq_b < SM2_N_Z)) (PreH35 : (0 <= B_r_eq_b)) (PreH36 : (A_r_eq_b < SM2_N_Z)) (PreH37 : (0 <= A_r_eq_b)) (PreH38 : (result_pre = b_pre)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_7_r_eq_b := add_mod_n_partial_solve_wit_7_r_eq_b_pure -> add_mod_n_partial_solve_wit_7_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_8_non_alias_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_N_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_N_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_8_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH17 : (x3_2 < U64_MOD)) (PreH18 : (0 <= x3_2)) (PreH19 : (x2_2 < U64_MOD)) (PreH20 : (0 <= x2_2)) (PreH21 : (x1_2 < U64_MOD)) (PreH22 : (0 <= x1_2)) (PreH23 : (x0_2 < U64_MOD)) (PreH24 : (0 <= x0_2)) (PreH25 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH26 : (x3 < U64_MOD)) (PreH27 : (0 <= x3)) (PreH28 : (x2 < U64_MOD)) (PreH29 : (0 <= x2)) (PreH30 : (x1 < U64_MOD)) (PreH31 : (0 <= x1)) (PreH32 : (x0 < U64_MOD)) (PreH33 : (0 <= x0)) (PreH34 : (B_non_alias < SM2_N_Z)) (PreH35 : (0 <= B_non_alias)) (PreH36 : (A_non_alias < SM2_N_Z)) (PreH37 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "tmp" ) )->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition add_mod_n_partial_solve_wit_8_non_alias := add_mod_n_partial_solve_wit_8_non_alias_pure -> add_mod_n_partial_solve_wit_8_non_alias_aux.

Definition add_mod_n_partial_solve_wit_9_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 0 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_10_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (0 <= out_4)) (PreH26 : (out_4 < U64_MOD)) (PreH27 : (0 <= retval_4)) (PreH28 : (retval_4 <= 1)) (PreH29 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH30 : (0 <= out_3)) (PreH31 : (out_3 < U64_MOD)) (PreH32 : (0 <= retval_3)) (PreH33 : (retval_3 <= 1)) (PreH34 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH35 : (0 <= out_2)) (PreH36 : (out_2 < U64_MOD)) (PreH37 : (0 <= retval_2)) (PreH38 : (retval_2 <= 1)) (PreH39 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval)) (PreH43 : (retval <= 1)) (PreH44 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH45 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH46 : (x3_2 < U64_MOD)) (PreH47 : (0 <= x3_2)) (PreH48 : (x2_2 < U64_MOD)) (PreH49 : (0 <= x2_2)) (PreH50 : (x1_2 < U64_MOD)) (PreH51 : (0 <= x1_2)) (PreH52 : (x0_2 < U64_MOD)) (PreH53 : (0 <= x0_2)) (PreH54 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (B_r_eq_b < SM2_N_Z)) (PreH64 : (0 <= B_r_eq_b)) (PreH65 : (A_r_eq_b < SM2_N_Z)) (PreH66 : (0 <= A_r_eq_b)) (PreH67 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (0 <= out_4)) (PreH26 : (out_4 < U64_MOD)) (PreH27 : (0 <= retval_4)) (PreH28 : (retval_4 <= 1)) (PreH29 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH30 : (0 <= out_3)) (PreH31 : (out_3 < U64_MOD)) (PreH32 : (0 <= retval_3)) (PreH33 : (retval_3 <= 1)) (PreH34 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH35 : (0 <= out_2)) (PreH36 : (out_2 < U64_MOD)) (PreH37 : (0 <= retval_2)) (PreH38 : (retval_2 <= 1)) (PreH39 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval)) (PreH43 : (retval <= 1)) (PreH44 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH45 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH46 : (x3_2 < U64_MOD)) (PreH47 : (0 <= x3_2)) (PreH48 : (x2_2 < U64_MOD)) (PreH49 : (0 <= x2_2)) (PreH50 : (x1_2 < U64_MOD)) (PreH51 : (0 <= x1_2)) (PreH52 : (x0_2 < U64_MOD)) (PreH53 : (0 <= x0_2)) (PreH54 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (B_r_eq_b < SM2_N_Z)) (PreH64 : (0 <= B_r_eq_b)) (PreH65 : (A_r_eq_b < SM2_N_Z)) (PreH66 : (0 <= A_r_eq_b)) (PreH67 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (0 <= out_4)) (PreH26 : (out_4 < U64_MOD)) (PreH27 : (0 <= retval_4)) (PreH28 : (retval_4 <= 1)) (PreH29 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH30 : (0 <= out_3)) (PreH31 : (out_3 < U64_MOD)) (PreH32 : (0 <= retval_3)) (PreH33 : (retval_3 <= 1)) (PreH34 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH35 : (0 <= out_2)) (PreH36 : (out_2 < U64_MOD)) (PreH37 : (0 <= retval_2)) (PreH38 : (retval_2 <= 1)) (PreH39 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval)) (PreH43 : (retval <= 1)) (PreH44 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH45 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH46 : (x3_2 < U64_MOD)) (PreH47 : (0 <= x3_2)) (PreH48 : (x2_2 < U64_MOD)) (PreH49 : (0 <= x2_2)) (PreH50 : (x1_2 < U64_MOD)) (PreH51 : (0 <= x1_2)) (PreH52 : (x0_2 < U64_MOD)) (PreH53 : (0 <= x0_2)) (PreH54 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (B_r_eq_b < SM2_N_Z)) (PreH64 : (0 <= B_r_eq_b)) (PreH65 : (A_r_eq_b < SM2_N_Z)) (PreH66 : (0 <= A_r_eq_b)) (PreH67 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_10_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_r_eq_b < SM2_N_Z)) (PreH40 : (0 <= B_r_eq_b)) (PreH41 : (A_r_eq_b < SM2_N_Z)) (PreH42 : (0 <= A_r_eq_b)) (PreH43 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_10_r_eq_b := add_mod_n_partial_solve_wit_10_r_eq_b_pure -> add_mod_n_partial_solve_wit_10_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_11_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &(( &( "tmp" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 0 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition add_mod_n_partial_solve_wit_12_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (0 <= out_4)) (PreH26 : (out_4 < U64_MOD)) (PreH27 : (0 <= retval_4)) (PreH28 : (retval_4 <= 1)) (PreH29 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH30 : (0 <= out_3)) (PreH31 : (out_3 < U64_MOD)) (PreH32 : (0 <= retval_3)) (PreH33 : (retval_3 <= 1)) (PreH34 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH35 : (0 <= out_2)) (PreH36 : (out_2 < U64_MOD)) (PreH37 : (0 <= retval_2)) (PreH38 : (retval_2 <= 1)) (PreH39 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval)) (PreH43 : (retval <= 1)) (PreH44 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH45 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH46 : (x3_2 < U64_MOD)) (PreH47 : (0 <= x3_2)) (PreH48 : (x2_2 < U64_MOD)) (PreH49 : (0 <= x2_2)) (PreH50 : (x1_2 < U64_MOD)) (PreH51 : (0 <= x1_2)) (PreH52 : (x0_2 < U64_MOD)) (PreH53 : (0 <= x0_2)) (PreH54 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (B_non_alias < SM2_N_Z)) (PreH64 : (0 <= B_non_alias)) (PreH65 : (A_non_alias < SM2_N_Z)) (PreH66 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (0 <= out_4)) (PreH26 : (out_4 < U64_MOD)) (PreH27 : (0 <= retval_4)) (PreH28 : (retval_4 <= 1)) (PreH29 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH30 : (0 <= out_3)) (PreH31 : (out_3 < U64_MOD)) (PreH32 : (0 <= retval_3)) (PreH33 : (retval_3 <= 1)) (PreH34 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH35 : (0 <= out_2)) (PreH36 : (out_2 < U64_MOD)) (PreH37 : (0 <= retval_2)) (PreH38 : (retval_2 <= 1)) (PreH39 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval)) (PreH43 : (retval <= 1)) (PreH44 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH45 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH46 : (x3_2 < U64_MOD)) (PreH47 : (0 <= x3_2)) (PreH48 : (x2_2 < U64_MOD)) (PreH49 : (0 <= x2_2)) (PreH50 : (x1_2 < U64_MOD)) (PreH51 : (0 <= x1_2)) (PreH52 : (x0_2 < U64_MOD)) (PreH53 : (0 <= x0_2)) (PreH54 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (B_non_alias < SM2_N_Z)) (PreH64 : (0 <= B_non_alias)) (PreH65 : (A_non_alias < SM2_N_Z)) (PreH66 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_2 <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x0_2 >= 0)) (PreH18 : (x1_2 >= 0)) (PreH19 : (x2_2 >= 0)) (PreH20 : (x3_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out_3 >= 0)) (PreH24 : (out_4 >= 0)) (PreH25 : (0 <= out_4)) (PreH26 : (out_4 < U64_MOD)) (PreH27 : (0 <= retval_4)) (PreH28 : (retval_4 <= 1)) (PreH29 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH30 : (0 <= out_3)) (PreH31 : (out_3 < U64_MOD)) (PreH32 : (0 <= retval_3)) (PreH33 : (retval_3 <= 1)) (PreH34 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH35 : (0 <= out_2)) (PreH36 : (out_2 < U64_MOD)) (PreH37 : (0 <= retval_2)) (PreH38 : (retval_2 <= 1)) (PreH39 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval)) (PreH43 : (retval <= 1)) (PreH44 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH45 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH46 : (x3_2 < U64_MOD)) (PreH47 : (0 <= x3_2)) (PreH48 : (x2_2 < U64_MOD)) (PreH49 : (0 <= x2_2)) (PreH50 : (x1_2 < U64_MOD)) (PreH51 : (0 <= x1_2)) (PreH52 : (x0_2 < U64_MOD)) (PreH53 : (0 <= x0_2)) (PreH54 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (B_non_alias < SM2_N_Z)) (PreH64 : (0 <= B_non_alias)) (PreH65 : (A_non_alias < SM2_N_Z)) (PreH66 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "borrow" ) )) # UChar  |-> 1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  ((( &( "carry" ) )) # UChar  |-> retval_4)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_12_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH21 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (B_non_alias < SM2_N_Z)) (PreH40 : (0 <= B_non_alias)) (PreH41 : (A_non_alias < SM2_N_Z)) (PreH42 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_12_non_alias := add_mod_n_partial_solve_wit_12_non_alias_pure -> add_mod_n_partial_solve_wit_12_non_alias_aux.

Definition add_mod_n_partial_solve_wit_13_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_r_eq_b < SM2_N_Z)) (PreH45 : (0 <= B_r_eq_b)) (PreH46 : (A_r_eq_b < SM2_N_Z)) (PreH47 : (0 <= A_r_eq_b)) (PreH48 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 1 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_14_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_r_eq_b < SM2_N_Z)) (PreH45 : (0 <= B_r_eq_b)) (PreH46 : (A_r_eq_b < SM2_N_Z)) (PreH47 : (0 <= A_r_eq_b)) (PreH48 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out_5 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (out_4 >= 0)) (PreH24 : (out_5 >= 0)) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_5)) (PreH33 : (retval_5 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_4)) (PreH38 : (retval_4 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_3)) (PreH43 : (retval_3 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH45 : (0 <= out_2)) (PreH46 : (out_2 < U64_MOD)) (PreH47 : (0 <= retval_2)) (PreH48 : (retval_2 <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH50 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_r_eq_b < SM2_N_Z)) (PreH69 : (0 <= B_r_eq_b)) (PreH70 : (A_r_eq_b < SM2_N_Z)) (PreH71 : (0 <= A_r_eq_b)) (PreH72 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out_5 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (out_4 >= 0)) (PreH24 : (out_5 >= 0)) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_5)) (PreH33 : (retval_5 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_4)) (PreH38 : (retval_4 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_3)) (PreH43 : (retval_3 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH45 : (0 <= out_2)) (PreH46 : (out_2 < U64_MOD)) (PreH47 : (0 <= retval_2)) (PreH48 : (retval_2 <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH50 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_r_eq_b < SM2_N_Z)) (PreH69 : (0 <= B_r_eq_b)) (PreH70 : (A_r_eq_b < SM2_N_Z)) (PreH71 : (0 <= A_r_eq_b)) (PreH72 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x1_2 <= UINT64_MAX)) (PreH6 : (x2_2 <= UINT64_MAX)) (PreH7 : (x3_2 <= UINT64_MAX)) (PreH8 : (out_2 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out_5 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x1_2 >= 0)) (PreH18 : (x2_2 >= 0)) (PreH19 : (x3_2 >= 0)) (PreH20 : (out_2 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_3 >= 0)) (PreH23 : (out_4 >= 0)) (PreH24 : (out_5 >= 0)) (PreH25 : (0 <= out_5)) (PreH26 : (out_5 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_4)) (PreH31 : (out_4 < U64_MOD)) (PreH32 : (0 <= retval_5)) (PreH33 : (retval_5 <= 1)) (PreH34 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH35 : (0 <= out_3)) (PreH36 : (out_3 < U64_MOD)) (PreH37 : (0 <= retval_4)) (PreH38 : (retval_4 <= 1)) (PreH39 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_3)) (PreH43 : (retval_3 <= 1)) (PreH44 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH45 : (0 <= out_2)) (PreH46 : (out_2 < U64_MOD)) (PreH47 : (0 <= retval_2)) (PreH48 : (retval_2 <= 1)) (PreH49 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH50 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH60 : (x3 < U64_MOD)) (PreH61 : (0 <= x3)) (PreH62 : (x2 < U64_MOD)) (PreH63 : (0 <= x2)) (PreH64 : (x1 < U64_MOD)) (PreH65 : (0 <= x1)) (PreH66 : (x0 < U64_MOD)) (PreH67 : (0 <= x0)) (PreH68 : (B_r_eq_b < SM2_N_Z)) (PreH69 : (0 <= B_r_eq_b)) (PreH70 : (A_r_eq_b < SM2_N_Z)) (PreH71 : (0 <= A_r_eq_b)) (PreH72 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_14_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_r_eq_b < SM2_N_Z)) (PreH45 : (0 <= B_r_eq_b)) (PreH46 : (A_r_eq_b < SM2_N_Z)) (PreH47 : (0 <= A_r_eq_b)) (PreH48 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_14_r_eq_b := add_mod_n_partial_solve_wit_14_r_eq_b_pure -> add_mod_n_partial_solve_wit_14_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_15_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out_2)) (PreH17 : (out_2 < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH21 : (0 <= out)) (PreH22 : (out < U64_MOD)) (PreH23 : (0 <= retval)) (PreH24 : (retval <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH26 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_non_alias < SM2_N_Z)) (PreH45 : (0 <= B_non_alias)) (PreH46 : (A_non_alias < SM2_N_Z)) (PreH47 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 1 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_16_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_non_alias < SM2_N_Z)) (PreH45 : (0 <= B_non_alias)) (PreH46 : (A_non_alias < SM2_N_Z)) (PreH47 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (x0 >= 0)) (PreH15 : (x1 >= 0)) (PreH16 : (x2 >= 0)) (PreH17 : (x3 >= 0)) (PreH18 : (x0_2 >= 0)) (PreH19 : (x1_2 >= 0)) (PreH20 : (x2_2 >= 0)) (PreH21 : (x3_2 >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out >= 0)) (PreH24 : (out_3 >= 0)) (PreH25 : (out_4 >= 0)) (PreH26 : (out_5 >= 0)) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH32 : (0 <= out_4)) (PreH33 : (out_4 < U64_MOD)) (PreH34 : (0 <= retval_5)) (PreH35 : (retval_5 <= 1)) (PreH36 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH37 : (0 <= out_3)) (PreH38 : (out_3 < U64_MOD)) (PreH39 : (0 <= retval_4)) (PreH40 : (retval_4 <= 1)) (PreH41 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH42 : (0 <= out)) (PreH43 : (out < U64_MOD)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH47 : (0 <= out_2)) (PreH48 : (out_2 < U64_MOD)) (PreH49 : (0 <= retval_2)) (PreH50 : (retval_2 <= 1)) (PreH51 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH52 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH53 : (x3_2 < U64_MOD)) (PreH54 : (0 <= x3_2)) (PreH55 : (x2_2 < U64_MOD)) (PreH56 : (0 <= x2_2)) (PreH57 : (x1_2 < U64_MOD)) (PreH58 : (0 <= x1_2)) (PreH59 : (x0_2 < U64_MOD)) (PreH60 : (0 <= x0_2)) (PreH61 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH62 : (x3 < U64_MOD)) (PreH63 : (0 <= x3)) (PreH64 : (x2 < U64_MOD)) (PreH65 : (0 <= x2)) (PreH66 : (x1 < U64_MOD)) (PreH67 : (0 <= x1)) (PreH68 : (x0 < U64_MOD)) (PreH69 : (0 <= x0)) (PreH70 : (B_non_alias < SM2_N_Z)) (PreH71 : (0 <= B_non_alias)) (PreH72 : (A_non_alias < SM2_N_Z)) (PreH73 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (x0 >= 0)) (PreH15 : (x1 >= 0)) (PreH16 : (x2 >= 0)) (PreH17 : (x3 >= 0)) (PreH18 : (x0_2 >= 0)) (PreH19 : (x1_2 >= 0)) (PreH20 : (x2_2 >= 0)) (PreH21 : (x3_2 >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out >= 0)) (PreH24 : (out_3 >= 0)) (PreH25 : (out_4 >= 0)) (PreH26 : (out_5 >= 0)) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH32 : (0 <= out_4)) (PreH33 : (out_4 < U64_MOD)) (PreH34 : (0 <= retval_5)) (PreH35 : (retval_5 <= 1)) (PreH36 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH37 : (0 <= out_3)) (PreH38 : (out_3 < U64_MOD)) (PreH39 : (0 <= retval_4)) (PreH40 : (retval_4 <= 1)) (PreH41 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH42 : (0 <= out)) (PreH43 : (out < U64_MOD)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH47 : (0 <= out_2)) (PreH48 : (out_2 < U64_MOD)) (PreH49 : (0 <= retval_2)) (PreH50 : (retval_2 <= 1)) (PreH51 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH52 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH53 : (x3_2 < U64_MOD)) (PreH54 : (0 <= x3_2)) (PreH55 : (x2_2 < U64_MOD)) (PreH56 : (0 <= x2_2)) (PreH57 : (x1_2 < U64_MOD)) (PreH58 : (0 <= x1_2)) (PreH59 : (x0_2 < U64_MOD)) (PreH60 : (0 <= x0_2)) (PreH61 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH62 : (x3 < U64_MOD)) (PreH63 : (0 <= x3)) (PreH64 : (x2 < U64_MOD)) (PreH65 : (0 <= x2)) (PreH66 : (x1 < U64_MOD)) (PreH67 : (0 <= x1)) (PreH68 : (x0 < U64_MOD)) (PreH69 : (0 <= x0)) (PreH70 : (B_non_alias < SM2_N_Z)) (PreH71 : (0 <= B_non_alias)) (PreH72 : (A_non_alias < SM2_N_Z)) (PreH73 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out <= UINT64_MAX)) (PreH11 : (out_3 <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (x0 >= 0)) (PreH15 : (x1 >= 0)) (PreH16 : (x2 >= 0)) (PreH17 : (x3 >= 0)) (PreH18 : (x0_2 >= 0)) (PreH19 : (x1_2 >= 0)) (PreH20 : (x2_2 >= 0)) (PreH21 : (x3_2 >= 0)) (PreH22 : (out_2 >= 0)) (PreH23 : (out >= 0)) (PreH24 : (out_3 >= 0)) (PreH25 : (out_4 >= 0)) (PreH26 : (out_5 >= 0)) (PreH27 : (0 <= out_5)) (PreH28 : (out_5 < U64_MOD)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH32 : (0 <= out_4)) (PreH33 : (out_4 < U64_MOD)) (PreH34 : (0 <= retval_5)) (PreH35 : (retval_5 <= 1)) (PreH36 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH37 : (0 <= out_3)) (PreH38 : (out_3 < U64_MOD)) (PreH39 : (0 <= retval_4)) (PreH40 : (retval_4 <= 1)) (PreH41 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH42 : (0 <= out)) (PreH43 : (out < U64_MOD)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH47 : (0 <= out_2)) (PreH48 : (out_2 < U64_MOD)) (PreH49 : (0 <= retval_2)) (PreH50 : (retval_2 <= 1)) (PreH51 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH52 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH53 : (x3_2 < U64_MOD)) (PreH54 : (0 <= x3_2)) (PreH55 : (x2_2 < U64_MOD)) (PreH56 : (0 <= x2_2)) (PreH57 : (x1_2 < U64_MOD)) (PreH58 : (0 <= x1_2)) (PreH59 : (x0_2 < U64_MOD)) (PreH60 : (0 <= x0_2)) (PreH61 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH62 : (x3 < U64_MOD)) (PreH63 : (0 <= x3)) (PreH64 : (x2 < U64_MOD)) (PreH65 : (0 <= x2)) (PreH66 : (x1 < U64_MOD)) (PreH67 : (0 <= x1)) (PreH68 : (x0 < U64_MOD)) (PreH69 : (0 <= x0)) (PreH70 : (B_non_alias < SM2_N_Z)) (PreH71 : (0 <= B_non_alias)) (PreH72 : (A_non_alias < SM2_N_Z)) (PreH73 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_16_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval: Z) (PreH1 : (0 <= out_5)) (PreH2 : (out_5 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_4)) (PreH7 : (out_4 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_3)) (PreH12 : (out_3 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH27 : (x3_2 < U64_MOD)) (PreH28 : (0 <= x3_2)) (PreH29 : (x2_2 < U64_MOD)) (PreH30 : (0 <= x2_2)) (PreH31 : (x1_2 < U64_MOD)) (PreH32 : (0 <= x1_2)) (PreH33 : (x0_2 < U64_MOD)) (PreH34 : (0 <= x0_2)) (PreH35 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH36 : (x3 < U64_MOD)) (PreH37 : (0 <= x3)) (PreH38 : (x2 < U64_MOD)) (PreH39 : (0 <= x2)) (PreH40 : (x1 < U64_MOD)) (PreH41 : (0 <= x1)) (PreH42 : (x0 < U64_MOD)) (PreH43 : (0 <= x0)) (PreH44 : (B_non_alias < SM2_N_Z)) (PreH45 : (0 <= B_non_alias)) (PreH46 : (A_non_alias < SM2_N_Z)) (PreH47 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_16_non_alias := add_mod_n_partial_solve_wit_16_non_alias_pure -> add_mod_n_partial_solve_wit_16_non_alias_aux.

Definition add_mod_n_partial_solve_wit_17_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_r_eq_b < SM2_N_Z)) (PreH50 : (0 <= B_r_eq_b)) (PreH51 : (A_r_eq_b < SM2_N_Z)) (PreH52 : (0 <= A_r_eq_b)) (PreH53 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 2 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_18_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_r_eq_b < SM2_N_Z)) (PreH50 : (0 <= B_r_eq_b)) (PreH51 : (A_r_eq_b < SM2_N_Z)) (PreH52 : (0 <= A_r_eq_b)) (PreH53 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_4 <= UINT64_MAX)) (PreH11 : (out_5 <= UINT64_MAX)) (PreH12 : (out_6 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out_2 >= 0)) (PreH20 : (out_3 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_4 >= 0)) (PreH23 : (out_5 >= 0)) (PreH24 : (out_6 >= 0)) (PreH25 : (0 <= out_6)) (PreH26 : (out_6 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_5)) (PreH31 : (out_5 < U64_MOD)) (PreH32 : (0 <= retval_6)) (PreH33 : (retval_6 <= 1)) (PreH34 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH35 : (0 <= out_4)) (PreH36 : (out_4 < U64_MOD)) (PreH37 : (0 <= retval_5)) (PreH38 : (retval_5 <= 1)) (PreH39 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_4)) (PreH43 : (retval_4 <= 1)) (PreH44 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH45 : (0 <= out_3)) (PreH46 : (out_3 < U64_MOD)) (PreH47 : (0 <= retval_3)) (PreH48 : (retval_3 <= 1)) (PreH49 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH50 : (0 <= out_2)) (PreH51 : (out_2 < U64_MOD)) (PreH52 : (0 <= retval_2)) (PreH53 : (retval_2 <= 1)) (PreH54 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH55 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (B_r_eq_b < SM2_N_Z)) (PreH74 : (0 <= B_r_eq_b)) (PreH75 : (A_r_eq_b < SM2_N_Z)) (PreH76 : (0 <= A_r_eq_b)) (PreH77 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_4 <= UINT64_MAX)) (PreH11 : (out_5 <= UINT64_MAX)) (PreH12 : (out_6 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out_2 >= 0)) (PreH20 : (out_3 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_4 >= 0)) (PreH23 : (out_5 >= 0)) (PreH24 : (out_6 >= 0)) (PreH25 : (0 <= out_6)) (PreH26 : (out_6 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_5)) (PreH31 : (out_5 < U64_MOD)) (PreH32 : (0 <= retval_6)) (PreH33 : (retval_6 <= 1)) (PreH34 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH35 : (0 <= out_4)) (PreH36 : (out_4 < U64_MOD)) (PreH37 : (0 <= retval_5)) (PreH38 : (retval_5 <= 1)) (PreH39 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_4)) (PreH43 : (retval_4 <= 1)) (PreH44 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH45 : (0 <= out_3)) (PreH46 : (out_3 < U64_MOD)) (PreH47 : (0 <= retval_3)) (PreH48 : (retval_3 <= 1)) (PreH49 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH50 : (0 <= out_2)) (PreH51 : (out_2 < U64_MOD)) (PreH52 : (0 <= retval_2)) (PreH53 : (retval_2 <= 1)) (PreH54 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH55 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (B_r_eq_b < SM2_N_Z)) (PreH74 : (0 <= B_r_eq_b)) (PreH75 : (A_r_eq_b < SM2_N_Z)) (PreH76 : (0 <= A_r_eq_b)) (PreH77 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (out_2 <= UINT64_MAX)) (PreH8 : (out_3 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_4 <= UINT64_MAX)) (PreH11 : (out_5 <= UINT64_MAX)) (PreH12 : (out_6 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x2_2 >= 0)) (PreH18 : (x3_2 >= 0)) (PreH19 : (out_2 >= 0)) (PreH20 : (out_3 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_4 >= 0)) (PreH23 : (out_5 >= 0)) (PreH24 : (out_6 >= 0)) (PreH25 : (0 <= out_6)) (PreH26 : (out_6 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_5)) (PreH31 : (out_5 < U64_MOD)) (PreH32 : (0 <= retval_6)) (PreH33 : (retval_6 <= 1)) (PreH34 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH35 : (0 <= out_4)) (PreH36 : (out_4 < U64_MOD)) (PreH37 : (0 <= retval_5)) (PreH38 : (retval_5 <= 1)) (PreH39 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_4)) (PreH43 : (retval_4 <= 1)) (PreH44 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH45 : (0 <= out_3)) (PreH46 : (out_3 < U64_MOD)) (PreH47 : (0 <= retval_3)) (PreH48 : (retval_3 <= 1)) (PreH49 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH50 : (0 <= out_2)) (PreH51 : (out_2 < U64_MOD)) (PreH52 : (0 <= retval_2)) (PreH53 : (retval_2 <= 1)) (PreH54 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH55 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (B_r_eq_b < SM2_N_Z)) (PreH74 : (0 <= B_r_eq_b)) (PreH75 : (A_r_eq_b < SM2_N_Z)) (PreH76 : (0 <= A_r_eq_b)) (PreH77 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_18_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_r_eq_b < SM2_N_Z)) (PreH50 : (0 <= B_r_eq_b)) (PreH51 : (A_r_eq_b < SM2_N_Z)) (PreH52 : (0 <= A_r_eq_b)) (PreH53 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_18_r_eq_b := add_mod_n_partial_solve_wit_18_r_eq_b_pure -> add_mod_n_partial_solve_wit_18_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_19_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH16 : (0 <= out_3)) (PreH17 : (out_3 < U64_MOD)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH21 : (0 <= out_2)) (PreH22 : (out_2 < U64_MOD)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH26 : (0 <= out)) (PreH27 : (out < U64_MOD)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_N_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_N_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 2 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_20_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_N_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_N_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (out_6 <= UINT64_MAX)) (PreH15 : (x0 >= 0)) (PreH16 : (x1 >= 0)) (PreH17 : (x2 >= 0)) (PreH18 : (x3 >= 0)) (PreH19 : (x0_2 >= 0)) (PreH20 : (x1_2 >= 0)) (PreH21 : (x2_2 >= 0)) (PreH22 : (x3_2 >= 0)) (PreH23 : (out_2 >= 0)) (PreH24 : (out_3 >= 0)) (PreH25 : (out >= 0)) (PreH26 : (out_4 >= 0)) (PreH27 : (out_5 >= 0)) (PreH28 : (out_6 >= 0)) (PreH29 : (0 <= out_6)) (PreH30 : (out_6 < U64_MOD)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH34 : (0 <= out_5)) (PreH35 : (out_5 < U64_MOD)) (PreH36 : (0 <= retval_6)) (PreH37 : (retval_6 <= 1)) (PreH38 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH39 : (0 <= out_4)) (PreH40 : (out_4 < U64_MOD)) (PreH41 : (0 <= retval_5)) (PreH42 : (retval_5 <= 1)) (PreH43 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH44 : (0 <= out)) (PreH45 : (out < U64_MOD)) (PreH46 : (0 <= retval_4)) (PreH47 : (retval_4 <= 1)) (PreH48 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH49 : (0 <= out_3)) (PreH50 : (out_3 < U64_MOD)) (PreH51 : (0 <= retval_3)) (PreH52 : (retval_3 <= 1)) (PreH53 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH54 : (0 <= out_2)) (PreH55 : (out_2 < U64_MOD)) (PreH56 : (0 <= retval_2)) (PreH57 : (retval_2 <= 1)) (PreH58 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH59 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH60 : (x3_2 < U64_MOD)) (PreH61 : (0 <= x3_2)) (PreH62 : (x2_2 < U64_MOD)) (PreH63 : (0 <= x2_2)) (PreH64 : (x1_2 < U64_MOD)) (PreH65 : (0 <= x1_2)) (PreH66 : (x0_2 < U64_MOD)) (PreH67 : (0 <= x0_2)) (PreH68 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH69 : (x3 < U64_MOD)) (PreH70 : (0 <= x3)) (PreH71 : (x2 < U64_MOD)) (PreH72 : (0 <= x2)) (PreH73 : (x1 < U64_MOD)) (PreH74 : (0 <= x1)) (PreH75 : (x0 < U64_MOD)) (PreH76 : (0 <= x0)) (PreH77 : (B_non_alias < SM2_N_Z)) (PreH78 : (0 <= B_non_alias)) (PreH79 : (A_non_alias < SM2_N_Z)) (PreH80 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (out_6 <= UINT64_MAX)) (PreH15 : (x0 >= 0)) (PreH16 : (x1 >= 0)) (PreH17 : (x2 >= 0)) (PreH18 : (x3 >= 0)) (PreH19 : (x0_2 >= 0)) (PreH20 : (x1_2 >= 0)) (PreH21 : (x2_2 >= 0)) (PreH22 : (x3_2 >= 0)) (PreH23 : (out_2 >= 0)) (PreH24 : (out_3 >= 0)) (PreH25 : (out >= 0)) (PreH26 : (out_4 >= 0)) (PreH27 : (out_5 >= 0)) (PreH28 : (out_6 >= 0)) (PreH29 : (0 <= out_6)) (PreH30 : (out_6 < U64_MOD)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH34 : (0 <= out_5)) (PreH35 : (out_5 < U64_MOD)) (PreH36 : (0 <= retval_6)) (PreH37 : (retval_6 <= 1)) (PreH38 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH39 : (0 <= out_4)) (PreH40 : (out_4 < U64_MOD)) (PreH41 : (0 <= retval_5)) (PreH42 : (retval_5 <= 1)) (PreH43 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH44 : (0 <= out)) (PreH45 : (out < U64_MOD)) (PreH46 : (0 <= retval_4)) (PreH47 : (retval_4 <= 1)) (PreH48 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH49 : (0 <= out_3)) (PreH50 : (out_3 < U64_MOD)) (PreH51 : (0 <= retval_3)) (PreH52 : (retval_3 <= 1)) (PreH53 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH54 : (0 <= out_2)) (PreH55 : (out_2 < U64_MOD)) (PreH56 : (0 <= retval_2)) (PreH57 : (retval_2 <= 1)) (PreH58 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH59 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH60 : (x3_2 < U64_MOD)) (PreH61 : (0 <= x3_2)) (PreH62 : (x2_2 < U64_MOD)) (PreH63 : (0 <= x2_2)) (PreH64 : (x1_2 < U64_MOD)) (PreH65 : (0 <= x1_2)) (PreH66 : (x0_2 < U64_MOD)) (PreH67 : (0 <= x0_2)) (PreH68 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH69 : (x3 < U64_MOD)) (PreH70 : (0 <= x3)) (PreH71 : (x2 < U64_MOD)) (PreH72 : (0 <= x2)) (PreH73 : (x1 < U64_MOD)) (PreH74 : (0 <= x1)) (PreH75 : (x0 < U64_MOD)) (PreH76 : (0 <= x0)) (PreH77 : (B_non_alias < SM2_N_Z)) (PreH78 : (0 <= B_non_alias)) (PreH79 : (A_non_alias < SM2_N_Z)) (PreH80 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out <= UINT64_MAX)) (PreH12 : (out_4 <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (out_6 <= UINT64_MAX)) (PreH15 : (x0 >= 0)) (PreH16 : (x1 >= 0)) (PreH17 : (x2 >= 0)) (PreH18 : (x3 >= 0)) (PreH19 : (x0_2 >= 0)) (PreH20 : (x1_2 >= 0)) (PreH21 : (x2_2 >= 0)) (PreH22 : (x3_2 >= 0)) (PreH23 : (out_2 >= 0)) (PreH24 : (out_3 >= 0)) (PreH25 : (out >= 0)) (PreH26 : (out_4 >= 0)) (PreH27 : (out_5 >= 0)) (PreH28 : (out_6 >= 0)) (PreH29 : (0 <= out_6)) (PreH30 : (out_6 < U64_MOD)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH34 : (0 <= out_5)) (PreH35 : (out_5 < U64_MOD)) (PreH36 : (0 <= retval_6)) (PreH37 : (retval_6 <= 1)) (PreH38 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH39 : (0 <= out_4)) (PreH40 : (out_4 < U64_MOD)) (PreH41 : (0 <= retval_5)) (PreH42 : (retval_5 <= 1)) (PreH43 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH44 : (0 <= out)) (PreH45 : (out < U64_MOD)) (PreH46 : (0 <= retval_4)) (PreH47 : (retval_4 <= 1)) (PreH48 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH49 : (0 <= out_3)) (PreH50 : (out_3 < U64_MOD)) (PreH51 : (0 <= retval_3)) (PreH52 : (retval_3 <= 1)) (PreH53 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH54 : (0 <= out_2)) (PreH55 : (out_2 < U64_MOD)) (PreH56 : (0 <= retval_2)) (PreH57 : (retval_2 <= 1)) (PreH58 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH59 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH60 : (x3_2 < U64_MOD)) (PreH61 : (0 <= x3_2)) (PreH62 : (x2_2 < U64_MOD)) (PreH63 : (0 <= x2_2)) (PreH64 : (x1_2 < U64_MOD)) (PreH65 : (0 <= x1_2)) (PreH66 : (x0_2 < U64_MOD)) (PreH67 : (0 <= x0_2)) (PreH68 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH69 : (x3 < U64_MOD)) (PreH70 : (0 <= x3)) (PreH71 : (x2 < U64_MOD)) (PreH72 : (0 <= x2)) (PreH73 : (x1 < U64_MOD)) (PreH74 : (0 <= x1)) (PreH75 : (x0 < U64_MOD)) (PreH76 : (0 <= x0)) (PreH77 : (B_non_alias < SM2_N_Z)) (PreH78 : (0 <= B_non_alias)) (PreH79 : (A_non_alias < SM2_N_Z)) (PreH80 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_20_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out: Z) (retval_4: Z) (out_4: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval: Z) (PreH1 : (0 <= out_6)) (PreH2 : (out_6 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_5)) (PreH7 : (out_5 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_4)) (PreH12 : (out_4 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (B_non_alias < SM2_N_Z)) (PreH50 : (0 <= B_non_alias)) (PreH51 : (A_non_alias < SM2_N_Z)) (PreH52 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_4 ) = (out_4 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_20_non_alias := add_mod_n_partial_solve_wit_20_non_alias_pure -> add_mod_n_partial_solve_wit_20_non_alias_aux.

Definition add_mod_n_partial_solve_wit_21_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_r_eq_b < SM2_N_Z)) (PreH55 : (0 <= B_r_eq_b)) (PreH56 : (A_r_eq_b < SM2_N_Z)) (PreH57 : (0 <= A_r_eq_b)) (PreH58 : (result_pre = b_pre)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 3 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_22_r_eq_b_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH21 : (0 <= out_4)) (PreH22 : (out_4 < U64_MOD)) (PreH23 : (0 <= retval_4)) (PreH24 : (retval_4 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH26 : (0 <= out_3)) (PreH27 : (out_3 < U64_MOD)) (PreH28 : (0 <= retval_3)) (PreH29 : (retval_3 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH31 : (0 <= out_2)) (PreH32 : (out_2 < U64_MOD)) (PreH33 : (0 <= retval_2)) (PreH34 : (retval_2 <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_r_eq_b < SM2_N_Z)) (PreH55 : (0 <= B_r_eq_b)) (PreH56 : (A_r_eq_b < SM2_N_Z)) (PreH57 : (0 <= A_r_eq_b)) (PreH58 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_5 <= UINT64_MAX)) (PreH11 : (out_6 <= UINT64_MAX)) (PreH12 : (out_7 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out_2 >= 0)) (PreH19 : (out_3 >= 0)) (PreH20 : (out_4 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_5 >= 0)) (PreH23 : (out_6 >= 0)) (PreH24 : (out_7 >= 0)) (PreH25 : (0 <= out_7)) (PreH26 : (out_7 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_6)) (PreH31 : (out_6 < U64_MOD)) (PreH32 : (0 <= retval_7)) (PreH33 : (retval_7 <= 1)) (PreH34 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH35 : (0 <= out_5)) (PreH36 : (out_5 < U64_MOD)) (PreH37 : (0 <= retval_6)) (PreH38 : (retval_6 <= 1)) (PreH39 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_5)) (PreH43 : (retval_5 <= 1)) (PreH44 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH45 : (0 <= out_4)) (PreH46 : (out_4 < U64_MOD)) (PreH47 : (0 <= retval_4)) (PreH48 : (retval_4 <= 1)) (PreH49 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH50 : (0 <= out_3)) (PreH51 : (out_3 < U64_MOD)) (PreH52 : (0 <= retval_3)) (PreH53 : (retval_3 <= 1)) (PreH54 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH55 : (0 <= out_2)) (PreH56 : (out_2 < U64_MOD)) (PreH57 : (0 <= retval_2)) (PreH58 : (retval_2 <= 1)) (PreH59 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH60 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH61 : (x3_2 < U64_MOD)) (PreH62 : (0 <= x3_2)) (PreH63 : (x2_2 < U64_MOD)) (PreH64 : (0 <= x2_2)) (PreH65 : (x1_2 < U64_MOD)) (PreH66 : (0 <= x1_2)) (PreH67 : (x0_2 < U64_MOD)) (PreH68 : (0 <= x0_2)) (PreH69 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH70 : (x3 < U64_MOD)) (PreH71 : (0 <= x3)) (PreH72 : (x2 < U64_MOD)) (PreH73 : (0 <= x2)) (PreH74 : (x1 < U64_MOD)) (PreH75 : (0 <= x1)) (PreH76 : (x0 < U64_MOD)) (PreH77 : (0 <= x0)) (PreH78 : (B_r_eq_b < SM2_N_Z)) (PreH79 : (0 <= B_r_eq_b)) (PreH80 : (A_r_eq_b < SM2_N_Z)) (PreH81 : (0 <= A_r_eq_b)) (PreH82 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_5 <= UINT64_MAX)) (PreH11 : (out_6 <= UINT64_MAX)) (PreH12 : (out_7 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out_2 >= 0)) (PreH19 : (out_3 >= 0)) (PreH20 : (out_4 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_5 >= 0)) (PreH23 : (out_6 >= 0)) (PreH24 : (out_7 >= 0)) (PreH25 : (0 <= out_7)) (PreH26 : (out_7 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_6)) (PreH31 : (out_6 < U64_MOD)) (PreH32 : (0 <= retval_7)) (PreH33 : (retval_7 <= 1)) (PreH34 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH35 : (0 <= out_5)) (PreH36 : (out_5 < U64_MOD)) (PreH37 : (0 <= retval_6)) (PreH38 : (retval_6 <= 1)) (PreH39 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_5)) (PreH43 : (retval_5 <= 1)) (PreH44 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH45 : (0 <= out_4)) (PreH46 : (out_4 < U64_MOD)) (PreH47 : (0 <= retval_4)) (PreH48 : (retval_4 <= 1)) (PreH49 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH50 : (0 <= out_3)) (PreH51 : (out_3 < U64_MOD)) (PreH52 : (0 <= retval_3)) (PreH53 : (retval_3 <= 1)) (PreH54 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH55 : (0 <= out_2)) (PreH56 : (out_2 < U64_MOD)) (PreH57 : (0 <= retval_2)) (PreH58 : (retval_2 <= 1)) (PreH59 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH60 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH61 : (x3_2 < U64_MOD)) (PreH62 : (0 <= x3_2)) (PreH63 : (x2_2 < U64_MOD)) (PreH64 : (0 <= x2_2)) (PreH65 : (x1_2 < U64_MOD)) (PreH66 : (0 <= x1_2)) (PreH67 : (x0_2 < U64_MOD)) (PreH68 : (0 <= x0_2)) (PreH69 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH70 : (x3 < U64_MOD)) (PreH71 : (0 <= x3)) (PreH72 : (x2 < U64_MOD)) (PreH73 : (0 <= x2)) (PreH74 : (x1 < U64_MOD)) (PreH75 : (0 <= x1)) (PreH76 : (x0 < U64_MOD)) (PreH77 : (0 <= x0)) (PreH78 : (B_r_eq_b < SM2_N_Z)) (PreH79 : (0 <= B_r_eq_b)) (PreH80 : (A_r_eq_b < SM2_N_Z)) (PreH81 : (0 <= A_r_eq_b)) (PreH82 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x3_2 <= UINT64_MAX)) (PreH6 : (out_2 <= UINT64_MAX)) (PreH7 : (out_3 <= UINT64_MAX)) (PreH8 : (out_4 <= UINT64_MAX)) (PreH9 : (out <= UINT64_MAX)) (PreH10 : (out_5 <= UINT64_MAX)) (PreH11 : (out_6 <= UINT64_MAX)) (PreH12 : (out_7 <= UINT64_MAX)) (PreH13 : (x0 >= 0)) (PreH14 : (x1 >= 0)) (PreH15 : (x2 >= 0)) (PreH16 : (x3 >= 0)) (PreH17 : (x3_2 >= 0)) (PreH18 : (out_2 >= 0)) (PreH19 : (out_3 >= 0)) (PreH20 : (out_4 >= 0)) (PreH21 : (out >= 0)) (PreH22 : (out_5 >= 0)) (PreH23 : (out_6 >= 0)) (PreH24 : (out_7 >= 0)) (PreH25 : (0 <= out_7)) (PreH26 : (out_7 < U64_MOD)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH30 : (0 <= out_6)) (PreH31 : (out_6 < U64_MOD)) (PreH32 : (0 <= retval_7)) (PreH33 : (retval_7 <= 1)) (PreH34 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH35 : (0 <= out_5)) (PreH36 : (out_5 < U64_MOD)) (PreH37 : (0 <= retval_6)) (PreH38 : (retval_6 <= 1)) (PreH39 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH40 : (0 <= out)) (PreH41 : (out < U64_MOD)) (PreH42 : (0 <= retval_5)) (PreH43 : (retval_5 <= 1)) (PreH44 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH45 : (0 <= out_4)) (PreH46 : (out_4 < U64_MOD)) (PreH47 : (0 <= retval_4)) (PreH48 : (retval_4 <= 1)) (PreH49 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH50 : (0 <= out_3)) (PreH51 : (out_3 < U64_MOD)) (PreH52 : (0 <= retval_3)) (PreH53 : (retval_3 <= 1)) (PreH54 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH55 : (0 <= out_2)) (PreH56 : (out_2 < U64_MOD)) (PreH57 : (0 <= retval_2)) (PreH58 : (retval_2 <= 1)) (PreH59 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH60 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH61 : (x3_2 < U64_MOD)) (PreH62 : (0 <= x3_2)) (PreH63 : (x2_2 < U64_MOD)) (PreH64 : (0 <= x2_2)) (PreH65 : (x1_2 < U64_MOD)) (PreH66 : (0 <= x1_2)) (PreH67 : (x0_2 < U64_MOD)) (PreH68 : (0 <= x0_2)) (PreH69 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH70 : (x3 < U64_MOD)) (PreH71 : (0 <= x3)) (PreH72 : (x2 < U64_MOD)) (PreH73 : (0 <= x2)) (PreH74 : (x1 < U64_MOD)) (PreH75 : (0 <= x1)) (PreH76 : (x0 < U64_MOD)) (PreH77 : (0 <= x0)) (PreH78 : (B_r_eq_b < SM2_N_Z)) (PreH79 : (0 <= B_r_eq_b)) (PreH80 : (A_r_eq_b < SM2_N_Z)) (PreH81 : (0 <= A_r_eq_b)) (PreH82 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_22_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH21 : (0 <= out_4)) (PreH22 : (out_4 < U64_MOD)) (PreH23 : (0 <= retval_4)) (PreH24 : (retval_4 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH26 : (0 <= out_3)) (PreH27 : (out_3 < U64_MOD)) (PreH28 : (0 <= retval_3)) (PreH29 : (retval_3 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH31 : (0 <= out_2)) (PreH32 : (out_2 < U64_MOD)) (PreH33 : (0 <= retval_2)) (PreH34 : (retval_2 <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH36 : (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_r_eq_b < SM2_N_Z)) (PreH55 : (0 <= B_r_eq_b)) (PreH56 : (A_r_eq_b < SM2_N_Z)) (PreH57 : (0 <= A_r_eq_b)) (PreH58 : (result_pre = b_pre)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_r_eq_b = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_r_eq_b = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= B_r_eq_b) ” 
  &&  “ (A_r_eq_b < SM2_N_Z) ” 
  &&  “ (0 <= A_r_eq_b) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_22_r_eq_b := add_mod_n_partial_solve_wit_22_r_eq_b_pure -> add_mod_n_partial_solve_wit_22_r_eq_b_aux.

Definition add_mod_n_partial_solve_wit_23_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out_5: Z) (retval_5: Z) (out_6: Z) (retval_6: Z) (out_7: Z) (retval_7: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval_7)) (PreH4 : (retval_7 <= 1)) (PreH5 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) ))) (PreH16 : (0 <= out_4)) (PreH17 : (out_4 < U64_MOD)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH21 : (0 <= out_3)) (PreH22 : (out_3 < U64_MOD)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH26 : (0 <= out_2)) (PreH27 : (out_2 < U64_MOD)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH31 : (0 <= out)) (PreH32 : (out < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH36 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_non_alias < SM2_N_Z)) (PreH55 : (0 <= B_non_alias)) (PreH56 : (A_non_alias < SM2_N_Z)) (PreH57 : (0 <= A_non_alias)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_7 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_5 ) = (out_6 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((out + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&(( &( "SM2_N" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_N" ) )->ₛ "v") 3 0 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_24_non_alias_pure := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH21 : (0 <= out_4)) (PreH22 : (out_4 < U64_MOD)) (PreH23 : (0 <= retval_4)) (PreH24 : (retval_4 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH26 : (0 <= out_3)) (PreH27 : (out_3 < U64_MOD)) (PreH28 : (0 <= retval_3)) (PreH29 : (retval_3 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH31 : (0 <= out_2)) (PreH32 : (out_2 < U64_MOD)) (PreH33 : (0 <= retval_2)) (PreH34 : (retval_2 <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH36 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_non_alias < SM2_N_Z)) (PreH55 : (0 <= B_non_alias)) (PreH56 : (A_non_alias < SM2_N_Z)) (PreH57 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
) \/
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (out_6 <= UINT64_MAX)) (PreH15 : (out_7 <= UINT64_MAX)) (PreH16 : (x0 >= 0)) (PreH17 : (x1 >= 0)) (PreH18 : (x2 >= 0)) (PreH19 : (x3 >= 0)) (PreH20 : (x0_2 >= 0)) (PreH21 : (x1_2 >= 0)) (PreH22 : (x2_2 >= 0)) (PreH23 : (x3_2 >= 0)) (PreH24 : (out_2 >= 0)) (PreH25 : (out_3 >= 0)) (PreH26 : (out_4 >= 0)) (PreH27 : (out >= 0)) (PreH28 : (out_5 >= 0)) (PreH29 : (out_6 >= 0)) (PreH30 : (out_7 >= 0)) (PreH31 : (0 <= out_7)) (PreH32 : (out_7 < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH36 : (0 <= out_6)) (PreH37 : (out_6 < U64_MOD)) (PreH38 : (0 <= retval_7)) (PreH39 : (retval_7 <= 1)) (PreH40 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH41 : (0 <= out_5)) (PreH42 : (out_5 < U64_MOD)) (PreH43 : (0 <= retval_6)) (PreH44 : (retval_6 <= 1)) (PreH45 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH46 : (0 <= out)) (PreH47 : (out < U64_MOD)) (PreH48 : (0 <= retval_5)) (PreH49 : (retval_5 <= 1)) (PreH50 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH51 : (0 <= out_4)) (PreH52 : (out_4 < U64_MOD)) (PreH53 : (0 <= retval_4)) (PreH54 : (retval_4 <= 1)) (PreH55 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH56 : (0 <= out_3)) (PreH57 : (out_3 < U64_MOD)) (PreH58 : (0 <= retval_3)) (PreH59 : (retval_3 <= 1)) (PreH60 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH61 : (0 <= out_2)) (PreH62 : (out_2 < U64_MOD)) (PreH63 : (0 <= retval_2)) (PreH64 : (retval_2 <= 1)) (PreH65 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH66 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH67 : (x3_2 < U64_MOD)) (PreH68 : (0 <= x3_2)) (PreH69 : (x2_2 < U64_MOD)) (PreH70 : (0 <= x2_2)) (PreH71 : (x1_2 < U64_MOD)) (PreH72 : (0 <= x1_2)) (PreH73 : (x0_2 < U64_MOD)) (PreH74 : (0 <= x0_2)) (PreH75 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH76 : (x3 < U64_MOD)) (PreH77 : (0 <= x3)) (PreH78 : (x2 < U64_MOD)) (PreH79 : (0 <= x2)) (PreH80 : (x1 < U64_MOD)) (PreH81 : (0 <= x1)) (PreH82 : (x0 < U64_MOD)) (PreH83 : (0 <= x0)) (PreH84 : (B_non_alias < SM2_N_Z)) (PreH85 : (0 <= B_non_alias)) (PreH86 : (A_non_alias < SM2_N_Z)) (PreH87 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
).

Definition add_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (out_6 <= UINT64_MAX)) (PreH15 : (out_7 <= UINT64_MAX)) (PreH16 : (x0 >= 0)) (PreH17 : (x1 >= 0)) (PreH18 : (x2 >= 0)) (PreH19 : (x3 >= 0)) (PreH20 : (x0_2 >= 0)) (PreH21 : (x1_2 >= 0)) (PreH22 : (x2_2 >= 0)) (PreH23 : (x3_2 >= 0)) (PreH24 : (out_2 >= 0)) (PreH25 : (out_3 >= 0)) (PreH26 : (out_4 >= 0)) (PreH27 : (out >= 0)) (PreH28 : (out_5 >= 0)) (PreH29 : (out_6 >= 0)) (PreH30 : (out_7 >= 0)) (PreH31 : (0 <= out_7)) (PreH32 : (out_7 < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH36 : (0 <= out_6)) (PreH37 : (out_6 < U64_MOD)) (PreH38 : (0 <= retval_7)) (PreH39 : (retval_7 <= 1)) (PreH40 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH41 : (0 <= out_5)) (PreH42 : (out_5 < U64_MOD)) (PreH43 : (0 <= retval_6)) (PreH44 : (retval_6 <= 1)) (PreH45 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH46 : (0 <= out)) (PreH47 : (out < U64_MOD)) (PreH48 : (0 <= retval_5)) (PreH49 : (retval_5 <= 1)) (PreH50 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH51 : (0 <= out_4)) (PreH52 : (out_4 < U64_MOD)) (PreH53 : (0 <= retval_4)) (PreH54 : (retval_4 <= 1)) (PreH55 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH56 : (0 <= out_3)) (PreH57 : (out_3 < U64_MOD)) (PreH58 : (0 <= retval_3)) (PreH59 : (retval_3 <= 1)) (PreH60 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH61 : (0 <= out_2)) (PreH62 : (out_2 < U64_MOD)) (PreH63 : (0 <= retval_2)) (PreH64 : (retval_2 <= 1)) (PreH65 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH66 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH67 : (x3_2 < U64_MOD)) (PreH68 : (0 <= x3_2)) (PreH69 : (x2_2 < U64_MOD)) (PreH70 : (0 <= x2_2)) (PreH71 : (x1_2 < U64_MOD)) (PreH72 : (0 <= x1_2)) (PreH73 : (x0_2 < U64_MOD)) (PreH74 : (0 <= x0_2)) (PreH75 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH76 : (x3 < U64_MOD)) (PreH77 : (0 <= x3)) (PreH78 : (x2 < U64_MOD)) (PreH79 : (0 <= x2)) (PreH80 : (x1 < U64_MOD)) (PreH81 : (0 <= x1)) (PreH82 : (x0 < U64_MOD)) (PreH83 : (0 <= x0)) (PreH84 : (B_non_alias < SM2_N_Z)) (PreH85 : (0 <= B_non_alias)) (PreH86 : (A_non_alias < SM2_N_Z)) (PreH87 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ”
.

Definition add_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (x0 <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0_2 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (out_2 <= UINT64_MAX)) (PreH10 : (out_3 <= UINT64_MAX)) (PreH11 : (out_4 <= UINT64_MAX)) (PreH12 : (out <= UINT64_MAX)) (PreH13 : (out_5 <= UINT64_MAX)) (PreH14 : (out_6 <= UINT64_MAX)) (PreH15 : (out_7 <= UINT64_MAX)) (PreH16 : (x0 >= 0)) (PreH17 : (x1 >= 0)) (PreH18 : (x2 >= 0)) (PreH19 : (x3 >= 0)) (PreH20 : (x0_2 >= 0)) (PreH21 : (x1_2 >= 0)) (PreH22 : (x2_2 >= 0)) (PreH23 : (x3_2 >= 0)) (PreH24 : (out_2 >= 0)) (PreH25 : (out_3 >= 0)) (PreH26 : (out_4 >= 0)) (PreH27 : (out >= 0)) (PreH28 : (out_5 >= 0)) (PreH29 : (out_6 >= 0)) (PreH30 : (out_7 >= 0)) (PreH31 : (0 <= out_7)) (PreH32 : (out_7 < U64_MOD)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH36 : (0 <= out_6)) (PreH37 : (out_6 < U64_MOD)) (PreH38 : (0 <= retval_7)) (PreH39 : (retval_7 <= 1)) (PreH40 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH41 : (0 <= out_5)) (PreH42 : (out_5 < U64_MOD)) (PreH43 : (0 <= retval_6)) (PreH44 : (retval_6 <= 1)) (PreH45 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH46 : (0 <= out)) (PreH47 : (out < U64_MOD)) (PreH48 : (0 <= retval_5)) (PreH49 : (retval_5 <= 1)) (PreH50 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH51 : (0 <= out_4)) (PreH52 : (out_4 < U64_MOD)) (PreH53 : (0 <= retval_4)) (PreH54 : (retval_4 <= 1)) (PreH55 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH56 : (0 <= out_3)) (PreH57 : (out_3 < U64_MOD)) (PreH58 : (0 <= retval_3)) (PreH59 : (retval_3 <= 1)) (PreH60 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH61 : (0 <= out_2)) (PreH62 : (out_2 < U64_MOD)) (PreH63 : (0 <= retval_2)) (PreH64 : (retval_2 <= 1)) (PreH65 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH66 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH67 : (x3_2 < U64_MOD)) (PreH68 : (0 <= x3_2)) (PreH69 : (x2_2 < U64_MOD)) (PreH70 : (0 <= x2_2)) (PreH71 : (x1_2 < U64_MOD)) (PreH72 : (0 <= x1_2)) (PreH73 : (x0_2 < U64_MOD)) (PreH74 : (0 <= x0_2)) (PreH75 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH76 : (x3 < U64_MOD)) (PreH77 : (0 <= x3)) (PreH78 : (x2 < U64_MOD)) (PreH79 : (0 <= x2)) (PreH80 : (x1 < U64_MOD)) (PreH81 : (0 <= x1)) (PreH82 : (x0 < U64_MOD)) (PreH83 : (0 <= x0)) (PreH84 : (B_non_alias < SM2_N_Z)) (PreH85 : (0 <= B_non_alias)) (PreH86 : (A_non_alias < SM2_N_Z)) (PreH87 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  ((( &( "borrow" ) )) # UChar  |-> retval)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  ((( &( "carry" ) )) # UChar  |-> retval_5)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ”
.

Definition add_mod_n_partial_solve_wit_24_non_alias_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (out_4: Z) (retval_4: Z) (out: Z) (retval_5: Z) (out_5: Z) (retval_6: Z) (out_6: Z) (retval_7: Z) (out_7: Z) (retval: Z) (PreH1 : (0 <= out_7)) (PreH2 : (out_7 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_6)) (PreH7 : (out_6 < U64_MOD)) (PreH8 : (0 <= retval_7)) (PreH9 : (retval_7 <= 1)) (PreH10 : (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) ))) (PreH11 : (0 <= out_5)) (PreH12 : (out_5 < U64_MOD)) (PreH13 : (0 <= retval_6)) (PreH14 : (retval_6 <= 1)) (PreH15 : (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_5)) (PreH19 : (retval_5 <= 1)) (PreH20 : (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) ))) (PreH21 : (0 <= out_4)) (PreH22 : (out_4 < U64_MOD)) (PreH23 : (0 <= retval_4)) (PreH24 : (retval_4 <= 1)) (PreH25 : (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) ))) (PreH26 : (0 <= out_3)) (PreH27 : (out_3 < U64_MOD)) (PreH28 : (0 <= retval_3)) (PreH29 : (retval_3 <= 1)) (PreH30 : (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH31 : (0 <= out_2)) (PreH32 : (out_2 < U64_MOD)) (PreH33 : (0 <= retval_2)) (PreH34 : (retval_2 <= 1)) (PreH35 : (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH36 : (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (B_non_alias < SM2_N_Z)) (PreH55 : (0 <= B_non_alias)) (PreH56 : (A_non_alias < SM2_N_Z)) (PreH57 : (0 <= A_non_alias)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ ((unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.lnot (Znth 3 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64))) ” 
  &&  “ (0 <= out_7) ” 
  &&  “ (out_7 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((out_4 + (unsigned_last_nbits ((Z.lnot (Znth 2 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_7 ) = (out_7 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_6) ” 
  &&  “ (out_6 < U64_MOD) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (((out_3 + (unsigned_last_nbits ((Z.lnot (Znth 1 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + retval_6 ) = (out_6 + (retval_7 * U64_MOD ) )) ” 
  &&  “ (0 <= out_5) ” 
  &&  “ (out_5 < U64_MOD) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (((out_2 + (unsigned_last_nbits ((Z.lnot (Znth 0 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) 0))) (64)) ) + 1 ) = (out_5 + (retval_6 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (((x3 + x3_2 ) + retval_4 ) = (out + (retval_5 * U64_MOD ) )) ” 
  &&  “ (0 <= out_4) ” 
  &&  “ (out_4 < U64_MOD) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (((x2 + x2_2 ) + retval_3 ) = (out_4 + (retval_4 * U64_MOD ) )) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (((x1 + x1_2 ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (((x0 + x0_2 ) + 0 ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (B_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (B_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= B_non_alias) ” 
  &&  “ (A_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= A_non_alias) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_7)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_6)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_5)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> out)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> out_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> out_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> out_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((b_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
.

Definition add_mod_n_partial_solve_wit_24_non_alias := add_mod_n_partial_solve_wit_24_non_alias_pure -> add_mod_n_partial_solve_wit_24_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_add_mod_n_safety_wit_1_r_eq_b : add_mod_n_safety_wit_1_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_2_non_alias : add_mod_n_safety_wit_2_non_alias.
Axiom proof_of_add_mod_n_safety_wit_3_r_eq_b : add_mod_n_safety_wit_3_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_4_r_eq_b : add_mod_n_safety_wit_4_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_5_r_eq_b : add_mod_n_safety_wit_5_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_6_non_alias : add_mod_n_safety_wit_6_non_alias.
Axiom proof_of_add_mod_n_safety_wit_7_non_alias : add_mod_n_safety_wit_7_non_alias.
Axiom proof_of_add_mod_n_safety_wit_8_non_alias : add_mod_n_safety_wit_8_non_alias.
Axiom proof_of_add_mod_n_safety_wit_9_r_eq_b : add_mod_n_safety_wit_9_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_10_r_eq_b : add_mod_n_safety_wit_10_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_11_r_eq_b : add_mod_n_safety_wit_11_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_12_non_alias : add_mod_n_safety_wit_12_non_alias.
Axiom proof_of_add_mod_n_safety_wit_13_non_alias : add_mod_n_safety_wit_13_non_alias.
Axiom proof_of_add_mod_n_safety_wit_14_non_alias : add_mod_n_safety_wit_14_non_alias.
Axiom proof_of_add_mod_n_safety_wit_15_r_eq_b : add_mod_n_safety_wit_15_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_16_r_eq_b : add_mod_n_safety_wit_16_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_17_r_eq_b : add_mod_n_safety_wit_17_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_18_non_alias : add_mod_n_safety_wit_18_non_alias.
Axiom proof_of_add_mod_n_safety_wit_19_non_alias : add_mod_n_safety_wit_19_non_alias.
Axiom proof_of_add_mod_n_safety_wit_20_non_alias : add_mod_n_safety_wit_20_non_alias.
Axiom proof_of_add_mod_n_safety_wit_21_r_eq_b : add_mod_n_safety_wit_21_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_22_r_eq_b : add_mod_n_safety_wit_22_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_23_r_eq_b : add_mod_n_safety_wit_23_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_24_non_alias : add_mod_n_safety_wit_24_non_alias.
Axiom proof_of_add_mod_n_safety_wit_25_non_alias : add_mod_n_safety_wit_25_non_alias.
Axiom proof_of_add_mod_n_safety_wit_26_non_alias : add_mod_n_safety_wit_26_non_alias.
Axiom proof_of_add_mod_n_safety_wit_27_r_eq_b : add_mod_n_safety_wit_27_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_28_non_alias : add_mod_n_safety_wit_28_non_alias.
Axiom proof_of_add_mod_n_safety_wit_29_r_eq_b : add_mod_n_safety_wit_29_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_30_r_eq_b : add_mod_n_safety_wit_30_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_31_r_eq_b : add_mod_n_safety_wit_31_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_32_non_alias : add_mod_n_safety_wit_32_non_alias.
Axiom proof_of_add_mod_n_safety_wit_33_non_alias : add_mod_n_safety_wit_33_non_alias.
Axiom proof_of_add_mod_n_safety_wit_34_non_alias : add_mod_n_safety_wit_34_non_alias.
Axiom proof_of_add_mod_n_safety_wit_35_r_eq_b : add_mod_n_safety_wit_35_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_36_r_eq_b : add_mod_n_safety_wit_36_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_37_r_eq_b : add_mod_n_safety_wit_37_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_38_non_alias : add_mod_n_safety_wit_38_non_alias.
Axiom proof_of_add_mod_n_safety_wit_39_non_alias : add_mod_n_safety_wit_39_non_alias.
Axiom proof_of_add_mod_n_safety_wit_40_non_alias : add_mod_n_safety_wit_40_non_alias.
Axiom proof_of_add_mod_n_safety_wit_41_r_eq_b : add_mod_n_safety_wit_41_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_42_r_eq_b : add_mod_n_safety_wit_42_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_43_r_eq_b : add_mod_n_safety_wit_43_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_44_non_alias : add_mod_n_safety_wit_44_non_alias.
Axiom proof_of_add_mod_n_safety_wit_45_non_alias : add_mod_n_safety_wit_45_non_alias.
Axiom proof_of_add_mod_n_safety_wit_46_non_alias : add_mod_n_safety_wit_46_non_alias.
Axiom proof_of_add_mod_n_safety_wit_47_r_eq_b : add_mod_n_safety_wit_47_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_48_r_eq_b : add_mod_n_safety_wit_48_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_49_r_eq_b : add_mod_n_safety_wit_49_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_50_non_alias : add_mod_n_safety_wit_50_non_alias.
Axiom proof_of_add_mod_n_safety_wit_51_non_alias : add_mod_n_safety_wit_51_non_alias.
Axiom proof_of_add_mod_n_safety_wit_52_non_alias : add_mod_n_safety_wit_52_non_alias.
Axiom proof_of_add_mod_n_safety_wit_53_r_eq_b : add_mod_n_safety_wit_53_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_54_non_alias : add_mod_n_safety_wit_54_non_alias.
Axiom proof_of_add_mod_n_safety_wit_55_r_eq_b : add_mod_n_safety_wit_55_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_56_non_alias : add_mod_n_safety_wit_56_non_alias.
Axiom proof_of_add_mod_n_safety_wit_57_r_eq_b : add_mod_n_safety_wit_57_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_58_non_alias : add_mod_n_safety_wit_58_non_alias.
Axiom proof_of_add_mod_n_safety_wit_59_r_eq_b : add_mod_n_safety_wit_59_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_60_non_alias : add_mod_n_safety_wit_60_non_alias.
Axiom proof_of_add_mod_n_safety_wit_61_r_eq_b : add_mod_n_safety_wit_61_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_62_non_alias : add_mod_n_safety_wit_62_non_alias.
Axiom proof_of_add_mod_n_safety_wit_63_r_eq_b : add_mod_n_safety_wit_63_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_64_non_alias : add_mod_n_safety_wit_64_non_alias.
Axiom proof_of_add_mod_n_safety_wit_65_r_eq_b : add_mod_n_safety_wit_65_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_66_non_alias : add_mod_n_safety_wit_66_non_alias.
Axiom proof_of_add_mod_n_safety_wit_67_r_eq_b : add_mod_n_safety_wit_67_r_eq_b.
Axiom proof_of_add_mod_n_safety_wit_68_non_alias : add_mod_n_safety_wit_68_non_alias.
Axiom proof_of_add_mod_n_entail_wit_1_1_r_eq_b : add_mod_n_entail_wit_1_1_r_eq_b.
Axiom proof_of_add_mod_n_entail_wit_1_2_non_alias : add_mod_n_entail_wit_1_2_non_alias.
Axiom proof_of_add_mod_n_entail_wit_2_1_r_eq_b : add_mod_n_entail_wit_2_1_r_eq_b.
Axiom proof_of_add_mod_n_entail_wit_2_2_non_alias : add_mod_n_entail_wit_2_2_non_alias.
Axiom proof_of_add_mod_n_entail_wit_3_1_r_eq_b : add_mod_n_entail_wit_3_1_r_eq_b.
Axiom proof_of_add_mod_n_entail_wit_3_2_non_alias : add_mod_n_entail_wit_3_2_non_alias.
Axiom proof_of_add_mod_n_entail_wit_4_r_eq_b : add_mod_n_entail_wit_4_r_eq_b.
Axiom proof_of_add_mod_n_entail_wit_5_non_alias : add_mod_n_entail_wit_5_non_alias.
Axiom proof_of_add_mod_n_entail_wit_6_1_non_alias : add_mod_n_entail_wit_6_1_non_alias.
Axiom proof_of_add_mod_n_entail_wit_6_2_non_alias : add_mod_n_entail_wit_6_2_non_alias.
Axiom proof_of_add_mod_n_entail_wit_7_1_r_eq_b : add_mod_n_entail_wit_7_1_r_eq_b.
Axiom proof_of_add_mod_n_entail_wit_7_2_r_eq_b : add_mod_n_entail_wit_7_2_r_eq_b.
Axiom proof_of_add_mod_n_return_wit_1_r_eq_b : add_mod_n_return_wit_1_r_eq_b.
Axiom proof_of_add_mod_n_return_wit_2_non_alias : add_mod_n_return_wit_2_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_1_r_eq_b_pure : add_mod_n_partial_solve_wit_1_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_1_r_eq_b : add_mod_n_partial_solve_wit_1_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_2_non_alias_pure : add_mod_n_partial_solve_wit_2_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_2_non_alias : add_mod_n_partial_solve_wit_2_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_3_r_eq_b_pure : add_mod_n_partial_solve_wit_3_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_3_r_eq_b : add_mod_n_partial_solve_wit_3_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_4_non_alias_pure : add_mod_n_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_4_non_alias : add_mod_n_partial_solve_wit_4_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_5_r_eq_b_pure : add_mod_n_partial_solve_wit_5_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_5_r_eq_b : add_mod_n_partial_solve_wit_5_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_6_non_alias_pure : add_mod_n_partial_solve_wit_6_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_6_non_alias : add_mod_n_partial_solve_wit_6_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_7_r_eq_b_pure : add_mod_n_partial_solve_wit_7_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_7_r_eq_b : add_mod_n_partial_solve_wit_7_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_8_non_alias_pure : add_mod_n_partial_solve_wit_8_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_8_non_alias : add_mod_n_partial_solve_wit_8_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_9_r_eq_b : add_mod_n_partial_solve_wit_9_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_10_r_eq_b_pure : add_mod_n_partial_solve_wit_10_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_10_r_eq_b : add_mod_n_partial_solve_wit_10_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_11_non_alias : add_mod_n_partial_solve_wit_11_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_12_non_alias_pure : add_mod_n_partial_solve_wit_12_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_12_non_alias : add_mod_n_partial_solve_wit_12_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_13_r_eq_b : add_mod_n_partial_solve_wit_13_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_14_r_eq_b_pure : add_mod_n_partial_solve_wit_14_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_14_r_eq_b : add_mod_n_partial_solve_wit_14_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_15_non_alias : add_mod_n_partial_solve_wit_15_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_16_non_alias_pure : add_mod_n_partial_solve_wit_16_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_16_non_alias : add_mod_n_partial_solve_wit_16_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_17_r_eq_b : add_mod_n_partial_solve_wit_17_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_18_r_eq_b_pure : add_mod_n_partial_solve_wit_18_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_18_r_eq_b : add_mod_n_partial_solve_wit_18_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_19_non_alias : add_mod_n_partial_solve_wit_19_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_20_non_alias_pure : add_mod_n_partial_solve_wit_20_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_20_non_alias : add_mod_n_partial_solve_wit_20_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_21_r_eq_b : add_mod_n_partial_solve_wit_21_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_22_r_eq_b_pure : add_mod_n_partial_solve_wit_22_r_eq_b_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_22_r_eq_b : add_mod_n_partial_solve_wit_22_r_eq_b.
Axiom proof_of_add_mod_n_partial_solve_wit_23_non_alias : add_mod_n_partial_solve_wit_23_non_alias.
Axiom proof_of_add_mod_n_partial_solve_wit_24_non_alias_pure : add_mod_n_partial_solve_wit_24_non_alias_pure.
Axiom proof_of_add_mod_n_partial_solve_wit_24_non_alias : add_mod_n_partial_solve_wit_24_non_alias.

End VC_Correct.
