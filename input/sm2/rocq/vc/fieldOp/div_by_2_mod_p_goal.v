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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_proof.

(*----- Function div_by_2_mod_p -----*)

Definition div_by_2_mod_p_safety_wit_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_4_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_5_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_6_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_7_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_8_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_9_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_10_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_11_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_12_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_13_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_14_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_15_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_16_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_17_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_18_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_19_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_20_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_21_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_22_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_23_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_24_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_2)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_25_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_26_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_27_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_28_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_29_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_30_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval_3)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_31_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_32_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_33_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_34_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_35_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_36_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_37_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_38_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_39_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_40_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_41_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_42_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_43_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_44_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_45_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_46_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_47_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_48_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_49_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_50_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_51_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_52_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_53_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_54_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_55_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_56_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_57_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_58_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_59_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_60_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_61_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_62_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_63_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_64_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_65_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_66_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_67_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_68_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_69_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_70_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_71_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_72_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_73_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_74_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_75_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_76_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_77_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_78_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_79_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_80_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_81_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_82_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_83_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_84_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_85_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_86_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_87_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_88_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_89_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_90_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_91_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_92_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_93_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_94_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_95_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_96_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_97_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_98_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_99_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_100_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_101_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_102_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_103_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_104_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_105_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_106_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_107_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_108_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_109_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_110_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_111_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition div_by_2_mod_p_safety_wit_112_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_113_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_114_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_115_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_116_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_117_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_118_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_119_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_120_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_121_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_122_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_123_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_124_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_125_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_126_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_127_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_128_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_129_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_130_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_131_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_132_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_133_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_134_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_135_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_136_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_137_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_138_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_139_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_140_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_141_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_142_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_143_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_144_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_145_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_146_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_147_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_148_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_149_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_150_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_151_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_152_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_153_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_154_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_155_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_156_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_157_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_158_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_159_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_160_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_161_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_162_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_163_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_164_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_165_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_166_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_167_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition div_by_2_mod_p_safety_wit_168_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_169_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_170_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition div_by_2_mod_p_safety_wit_171_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_172_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_173_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_174_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_175_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_176_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_177_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_178_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_179_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_180_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_181_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_182_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_183_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_184_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition div_by_2_mod_p_safety_wit_185_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition div_by_2_mod_p_safety_wit_186_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition div_by_2_mod_p_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (result_pre <> a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (result_pre <> a_pre) ”
  &&  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_entail_wit_1_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
|--
  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias < SM2_P_Z)) (PreH2 : (0 <= A_non_alias)) (PreH3 : (result_pre <> a_pre)) ,
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
  &&  “ (result_pre <> a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_entail_wit_2_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (A_in_place < SM2_P_Z)) (PreH2 : (0 <= A_in_place)) (PreH3 : (result_pre = a_pre)) ,
  (store_u256 a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_entail_wit_3_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) ,
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
  &&  “ (result_pre <> a_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_entail_wit_3_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition div_by_2_mod_p_entail_wit_4_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_non_alias < SM2_P_Z)) (PreH31 : (0 <= A_non_alias)) (PreH32 : (result_pre <> a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  EX (T: Z) ,
  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (retval * U256_MOD ) )) ”
  &&  (store_u256 ( &( "tmp" ) ) T )
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_non_alias < SM2_P_Z)) (PreH31 : (0 <= A_non_alias)) (PreH32 : (result_pre <> a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  TT && emp 
|--
  “ ((fp_div2_adjusted (A_non_alias)) = ((u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))) + (retval * U256_MOD ) )) ” 
  &&  “ ((u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))) < U256_MOD) ” 
  &&  “ (0 <= (u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))))))))))) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias) ”
  &&  emp
).

Definition div_by_2_mod_p_entail_wit_4_non_alias_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_non_alias < SM2_P_Z)) (PreH31 : (0 <= A_non_alias)) (PreH32 : (result_pre <> a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((fp_div2_adjusted (A_non_alias)) = ((u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))) + (retval * U256_MOD ) ))
.

Definition div_by_2_mod_p_entail_wit_4_non_alias_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_non_alias < SM2_P_Z)) (PreH31 : (0 <= A_non_alias)) (PreH32 : (result_pre <> a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))) < U256_MOD)
.

Definition div_by_2_mod_p_entail_wit_4_non_alias_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_non_alias < SM2_P_Z)) (PreH31 : (0 <= A_non_alias)) (PreH32 : (result_pre <> a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (0 <= (u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))))
.

Definition div_by_2_mod_p_entail_wit_4_non_alias_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_non_alias < SM2_P_Z)) (PreH31 : (0 <= A_non_alias)) (PreH32 : (result_pre <> a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = A_non_alias)
.

Definition div_by_2_mod_p_entail_wit_5_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_in_place < SM2_P_Z)) (PreH31 : (0 <= A_in_place)) (PreH32 : (result_pre = a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  EX (T: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (retval * U256_MOD ) )) ”
  &&  (store_u256 ( &( "tmp" ) ) T )
  **  (store_fp result_pre A_in_place )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval_4: Z) (out_4: Z) (retval: Z) (PreH1 : (0 <= out_4)) (PreH2 : (out_4 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) + (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_4 ) = (out_4 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_3)) (PreH7 : (out_3 < U64_MOD)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval_4 * U64_MOD ) ))) (PreH11 : (0 <= out_2)) (PreH12 : (out_2 < U64_MOD)) (PreH13 : (0 <= retval_3)) (PreH14 : (retval_3 <= 1)) (PreH15 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH16 : (0 <= out)) (PreH17 : (out < U64_MOD)) (PreH18 : (0 <= retval_2)) (PreH19 : (retval_2 <= 1)) (PreH20 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH21 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH22 : (x3 < U64_MOD)) (PreH23 : (0 <= x3)) (PreH24 : (x2 < U64_MOD)) (PreH25 : (0 <= x2)) (PreH26 : (x1 < U64_MOD)) (PreH27 : (0 <= x1)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (A_in_place < SM2_P_Z)) (PreH31 : (0 <= A_in_place)) (PreH32 : (result_pre = a_pre)) (PreH33 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= (u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))))))))))))) ” 
  &&  “ ((u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))) < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = ((u64_list_value ((replace_Znth (3) (out_4) ((replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))))))) + (retval * U256_MOD ) )) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
).

Definition div_by_2_mod_p_entail_wit_6_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (T: Z) (C: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= T)) (PreH3 : (T < U256_MOD)) (PreH4 : (0 <= C)) (PreH5 : (C <= 1)) (PreH6 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) ,
  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_u256 ( &( "tmp" ) ) T )
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_fp result_pre A_in_place )
  **  (store_sm2_p )
|--
  (“ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ”
  &&  (store_u256 result_pre A_in_place )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_u256 ( &( "tmp" ) ) T )
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p ))
  ||
  (EX (C_2: Z)  (T_2: Z) ,
  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 ( &( "tmp" ) ) T_2 )
  **  ((( &( "carry" ) )) # UChar  |-> C_2)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
.

Definition div_by_2_mod_p_entail_wit_6_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (T_2: Z) (C_2: Z) (PreH1 : (0 <= T_2)) (PreH2 : (T_2 < U256_MOD)) (PreH3 : (0 <= C_2)) (PreH4 : (C_2 <= 1)) (PreH5 : ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) ))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 ( &( "tmp" ) ) T_2 )
  **  ((( &( "carry" ) )) # UChar  |-> C_2)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (EX (C: Z)  (T: Z) ,
  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ”
  &&  (store_u256 result_pre A_in_place )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_u256 ( &( "tmp" ) ) T )
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p ))
  ||
  (“ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 ( &( "tmp" ) ) T_2 )
  **  ((( &( "carry" ) )) # UChar  |-> C_2)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
.

Definition div_by_2_mod_p_entail_wit_7_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (T: Z) (C: Z) (PreH1 : (A_in_place < SM2_P_Z)) (PreH2 : (0 <= A_in_place)) (PreH3 : (result_pre = a_pre)) (PreH4 : (0 <= T)) (PreH5 : (T < U256_MOD)) (PreH6 : (0 <= C)) (PreH7 : (C <= 1)) (PreH8 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) ,
  (store_u256 result_pre A_in_place )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_u256 ( &( "tmp" ) ) T )
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (C_2: Z)  (T_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C_2)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
.

Definition div_by_2_mod_p_entail_wit_7_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (T_2: Z) (C_2: Z) (PreH1 : (A_non_alias < SM2_P_Z)) (PreH2 : (0 <= A_non_alias)) (PreH3 : (0 <= T_2)) (PreH4 : (T_2 < U256_MOD)) (PreH5 : (0 <= C_2)) (PreH6 : (C_2 <= 1)) (PreH7 : ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) ))) ,
  (store_u256 a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 ( &( "tmp" ) ) T_2 )
  **  ((( &( "carry" ) )) # UChar  |-> C_2)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (C: Z)  (T: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C)
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> C_2)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
.

Definition div_by_2_mod_p_entail_wit_8_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p )
|--
  (“ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (C_2: Z)  (T_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ” 
  &&  “ (C_2 = 0) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x0_5: Z)  (x1_5: Z)  (x2_5: Z)  (x3_5: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition div_by_2_mod_p_entail_wit_8_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (T_2: Z) (C_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T_2)) (PreH22 : (T_2 < U256_MOD)) (PreH23 : (0 <= C_2)) (PreH24 : (C_2 <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) ))) (PreH26 : (C_2 = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (C: Z)  (T: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p ))
  ||
  (“ (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ” 
  &&  “ (C_2 = 0) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (EX (x0_5: Z)  (x1_5: Z)  (x2_5: Z)  (x3_5: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (x0_6: Z)  (x1_6: Z)  (x2_6: Z)  (x3_6: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition div_by_2_mod_p_entail_wit_8_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH2 : (x3_5 < U64_MOD)) (PreH3 : (0 <= x3_5)) (PreH4 : (x2_5 < U64_MOD)) (PreH5 : (0 <= x2_5)) (PreH6 : (x1_5 < U64_MOD)) (PreH7 : (0 <= x1_5)) (PreH8 : (x0_5 < U64_MOD)) (PreH9 : (0 <= x0_5)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (C: Z)  (T: Z) ,
  “ (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_sm2_p ))
  ||
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (C_2: Z)  (T_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ” 
  &&  “ (C_2 = 0) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (A_in_place = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_5) ((cons (x1_5) ((cons (x2_5) ((cons (x3_5) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition div_by_2_mod_p_entail_wit_8_4_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH2 : (x3_6 < U64_MOD)) (PreH3 : (0 <= x3_6)) (PreH4 : (x2_6 < U64_MOD)) (PreH5 : (0 <= x2_6)) (PreH6 : (x1_6 < U64_MOD)) (PreH7 : (0 <= x1_6)) (PreH8 : (x0_6 < U64_MOD)) (PreH9 : (0 <= x0_6)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (C_2: Z)  (T_2: Z) ,
  “ (A_non_alias = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (T_2 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (0 <= T_2) ” 
  &&  “ (T_2 < U256_MOD) ” 
  &&  “ (0 <= C_2) ” 
  &&  “ (C_2 <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T_2 + (C_2 * U256_MOD ) )) ” 
  &&  “ (C_2 = 0) ”
  &&  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  ||
  (“ (A_non_alias = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (A_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= A_non_alias) ” 
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0_6) ((cons (x1_6) ((cons (x2_6) ((cons (x3_6) ((@nil Z)))))))))) (0)))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 ))
.

Definition div_by_2_mod_p_return_wit_1_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (store_sm2_p )
|--
  “ (result_pre = a_pre) ”
  &&  (store_fp result_pre (fp_div2 (A_in_place)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  TT && emp 
|--
  “ (0 <= (fp_div2 (A_in_place))) ” 
  &&  “ ((fp_div2 (A_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63))) ” 
  &&  “ ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)) < U64_MOD) ” 
  &&  “ ((fp_div2 (A_in_place)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63))))) ”
  &&  emp
).

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (0 <= (fp_div2 (A_in_place)))
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  ((fp_div2 (A_in_place)) < SM2_P_Z)
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_5 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_6 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_7 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_8 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_9 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)))
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_10 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_1_in_place_split_goal_11 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C <> 0)) ,
  ((fp_div2 (A_in_place)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)))))
.

Definition div_by_2_mod_p_return_wit_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_p )
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (fp_div2 (A_non_alias)) )
  **  (store_sm2_p )
) \/
(
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  TT && emp 
|--
  “ (0 <= (fp_div2 (A_non_alias))) ” 
  &&  “ ((fp_div2 (A_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63))) ” 
  &&  “ ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)) < U64_MOD) ” 
  &&  “ ((fp_div2 (A_non_alias)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63))))) ”
  &&  emp
).

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (0 <= (fp_div2 (A_non_alias)))
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  ((fp_div2 (A_non_alias)) < SM2_P_Z)
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_4 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_5 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_6 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_7 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_8 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_9 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (0 <= (Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)))
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_10 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_2_non_alias_split_goal_11 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  ((fp_div2 (A_non_alias)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.lor (Z.shiftr x3 1) (Z.shiftl 1 63)))))
.

Definition div_by_2_mod_p_return_wit_3_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.shiftr x3 1))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (store_sm2_p )
|--
  “ (result_pre = a_pre) ”
  &&  (store_fp result_pre (fp_div2 (A_in_place)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  TT && emp 
|--
  “ (0 <= (fp_div2 (A_in_place))) ” 
  &&  “ ((fp_div2 (A_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.shiftr x3 1)) ” 
  &&  “ ((Z.shiftr x3 1) < U64_MOD) ” 
  &&  “ ((fp_div2 (A_in_place)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.shiftr x3 1)))) ”
  &&  emp
).

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (0 <= (fp_div2 (A_in_place)))
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  ((fp_div2 (A_in_place)) < SM2_P_Z)
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_5 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_6 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_7 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_8 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_9 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  (0 <= (Z.shiftr x3 1))
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_10 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  ((Z.shiftr x3 1) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_3_in_place_split_goal_11 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_in_place < SM2_P_Z)) (PreH20 : (0 <= A_in_place)) (PreH21 : (result_pre = a_pre)) (PreH22 : (0 <= T)) (PreH23 : (T < U256_MOD)) (PreH24 : (0 <= C)) (PreH25 : (C <= 1)) (PreH26 : ((fp_div2_adjusted (A_in_place)) = (T + (C * U256_MOD ) ))) (PreH27 : (C = 0)) ,
  ((fp_div2 (A_in_place)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.shiftr x3 1))))
.

Definition div_by_2_mod_p_return_wit_4_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.shiftr x3 1))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_p )
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (fp_div2 (A_non_alias)) )
  **  (store_sm2_p )
) \/
(
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  TT && emp 
|--
  “ (0 <= (fp_div2 (A_non_alias))) ” 
  &&  “ ((fp_div2 (A_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.shiftr x3 1)) ” 
  &&  “ ((Z.shiftr x3 1) < U64_MOD) ” 
  &&  “ ((fp_div2 (A_non_alias)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.shiftr x3 1)))) ”
  &&  emp
).

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (0 <= (fp_div2 (A_non_alias)))
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  ((fp_div2 (A_non_alias)) < SM2_P_Z)
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (0 <= (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_4 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_5 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (0 <= (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_6 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_7 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (0 <= (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_8 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_9 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (0 <= (Z.shiftr x3 1))
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_10 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  ((Z.shiftr x3 1) < U64_MOD)
.

Definition div_by_2_mod_p_return_wit_4_non_alias_split_goal_11 := 
forall (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  ((fp_div2 (A_non_alias)) = (u256_of_limbs ((Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64)))) ((Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64)))) ((Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64)))) ((Z.shiftr x3 1))))
.

Definition div_by_2_mod_p_return_wit_5_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (result_pre = a_pre) ”
  &&  (store_fp result_pre (fp_div2 (A_in_place)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (fp_div2 (A_in_place))) ” 
  &&  “ ((fp_div2 (A_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)) ” 
  &&  “ ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) < U64_MOD) ” 
  &&  “ ((fp_div2 (A_in_place)) = (u256_of_limbs ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)))) ”
  &&  (store_sm2_p )
).

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (fp_div2 (A_in_place))) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((fp_div2 (A_in_place)) < SM2_P_Z) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_5 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_6 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_7 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_8 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_9 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_10 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_11 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((fp_div2 (A_in_place)) = (u256_of_limbs ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)))) ”
.

Definition div_by_2_mod_p_return_wit_5_in_place_split_goal_spatial := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_in_place < SM2_P_Z)) (PreH19 : (0 <= A_in_place)) (PreH20 : (result_pre = a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  (store_sm2_p )
.

Definition div_by_2_mod_p_return_wit_6_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (fp_div2 (A_non_alias)) )
  **  (store_sm2_p )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ” 
  &&  “ ((Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ” 
  &&  “ (0 <= (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ” 
  &&  “ ((Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ” 
  &&  “ (0 <= (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ” 
  &&  “ ((Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ” 
  &&  “ (0 <= (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ” 
  &&  “ ((Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ” 
  &&  “ (A_non_alias = (u256_of_limbs ((Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ((Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ((Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ((Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))))) ” 
  &&  “ (0 <= (fp_div2 (A_non_alias))) ” 
  &&  “ ((fp_div2 (A_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ” 
  &&  “ ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ” 
  &&  “ (0 <= (Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)) ” 
  &&  “ ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) < U64_MOD) ” 
  &&  “ ((fp_div2 (A_non_alias)) = (u256_of_limbs ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)))) ”
  &&  (store_sm2_p )
).

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_5 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_6 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_7 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_8 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_9 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (A_non_alias = (u256_of_limbs ((Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ((Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ((Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))) ((Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0))))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_10 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (fp_div2 (A_non_alias))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_11 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((fp_div2 (A_non_alias)) < SM2_P_Z) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_12 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_13 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_14 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_15 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_16 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_17 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_18 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ (0 <= (Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_19 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) < U64_MOD) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_20 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  “ ((fp_div2 (A_non_alias)) = (u256_of_limbs ((Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64)))) ((Z.shiftr (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1)))) ”
.

Definition div_by_2_mod_p_return_wit_6_non_alias_split_goal_spatial := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH2 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH3 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH4 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) <= UINT64_MAX)) (PreH5 : ((Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH6 : ((Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH7 : ((Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH8 : ((Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)) >= 0)) (PreH9 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH10 : (x3 < U64_MOD)) (PreH11 : (0 <= x3)) (PreH12 : (x2 < U64_MOD)) (PreH13 : (0 <= x2)) (PreH14 : (x1 < U64_MOD)) (PreH15 : (0 <= x1)) (PreH16 : (x0 < U64_MOD)) (PreH17 : (0 <= x0)) (PreH18 : (A_non_alias < SM2_P_Z)) (PreH19 : (0 <= A_non_alias)) (PreH20 : (result_pre <> a_pre)) (PreH21 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
|--
  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) ,
  (UndefStructPredu32 ( &( "tmp" ) ) )
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
  &&  “ (result_pre <> a_pre) ”
  &&  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 0 0 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
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
  &&  “ (result_pre <> a_pre) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 0 0 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_5_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 0 0 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_6_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 0 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_7_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_7_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_7_in_place_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_7_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 0 0 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_7_in_place := div_by_2_mod_p_partial_solve_wit_7_in_place_pure -> div_by_2_mod_p_partial_solve_wit_7_in_place_aux.

Definition div_by_2_mod_p_partial_solve_wit_8_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 0 0 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_9_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 0 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_10_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_10_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_10_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ ((Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 0 0 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_10_non_alias := div_by_2_mod_p_partial_solve_wit_10_non_alias_pure -> div_by_2_mod_p_partial_solve_wit_10_non_alias_aux.

Definition div_by_2_mod_p_partial_solve_wit_11_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 1 0 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_12_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 1 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_13_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_13_in_place_pure_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_13_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_in_place < SM2_P_Z)) (PreH16 : (0 <= A_in_place)) (PreH17 : (result_pre = a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 1 0 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_13_in_place := div_by_2_mod_p_partial_solve_wit_13_in_place_pure -> div_by_2_mod_p_partial_solve_wit_13_in_place_aux.

Definition div_by_2_mod_p_partial_solve_wit_14_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 1 0 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_15_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 1 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias_pure_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (PreH1 : (0 <= out)) (PreH2 : (out < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH6 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH7 : (x3 < U64_MOD)) (PreH8 : (0 <= x3)) (PreH9 : (x2 < U64_MOD)) (PreH10 : (0 <= x2)) (PreH11 : (x1 < U64_MOD)) (PreH12 : (0 <= x1)) (PreH13 : (x0 < U64_MOD)) (PreH14 : (0 <= x0)) (PreH15 : (A_non_alias < SM2_P_Z)) (PreH16 : (0 <= A_non_alias)) (PreH17 : (result_pre <> a_pre)) (PreH18 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0)) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 1 0 4 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_16_non_alias := div_by_2_mod_p_partial_solve_wit_16_non_alias_pure -> div_by_2_mod_p_partial_solve_wit_16_non_alias_aux.

Definition div_by_2_mod_p_partial_solve_wit_17_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 2 0 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_18_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 2 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_19_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_19_in_place_pure_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_19_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_in_place < SM2_P_Z)) (PreH21 : (0 <= A_in_place)) (PreH22 : (result_pre = a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 2 0 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_19_in_place := div_by_2_mod_p_partial_solve_wit_19_in_place_pure -> div_by_2_mod_p_partial_solve_wit_19_in_place_aux.

Definition div_by_2_mod_p_partial_solve_wit_20_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 2 0 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_21_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 2 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias_pure_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval: Z) (PreH1 : (0 <= out_2)) (PreH2 : (out_2 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out)) (PreH7 : (out < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH11 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (A_non_alias < SM2_P_Z)) (PreH21 : (0 <= A_non_alias)) (PreH22 : (result_pre <> a_pre)) (PreH23 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0)) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 2 0 4 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_22_non_alias := div_by_2_mod_p_partial_solve_wit_22_non_alias_pure -> div_by_2_mod_p_partial_solve_wit_22_non_alias_aux.

Definition div_by_2_mod_p_partial_solve_wit_23_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 3 0 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_24_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 3 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_25_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ” 
  &&  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_25_in_place_pure_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_25_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_in_place < SM2_P_Z)) (PreH26 : (0 <= A_in_place)) (PreH27 : (result_pre = a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 3 0 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
.

Definition div_by_2_mod_p_partial_solve_wit_25_in_place := div_by_2_mod_p_partial_solve_wit_25_in_place_pure -> div_by_2_mod_p_partial_solve_wit_25_in_place_aux.

Definition div_by_2_mod_p_partial_solve_wit_26_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 3 0 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_27_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval: Z) (out_2: Z) (retval_2: Z) (out_3: Z) (retval_3: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_3 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval ) = (out_2 + (retval_2 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0))
  **  (UInt64Array.missing_i &(( &( "SM2_P" ) )->ₛ "v") 3 0 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ” 
  &&  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
).

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ”
.

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias_pure_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  ((( &( "carry" ) )) # UChar  |-> retval)
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ”
.

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (out: Z) (retval_2: Z) (out_2: Z) (retval_3: Z) (out_3: Z) (retval: Z) (PreH1 : (0 <= out_3)) (PreH2 : (out_3 < U64_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) ))) (PreH6 : (0 <= out_2)) (PreH7 : (out_2 < U64_MOD)) (PreH8 : (0 <= retval_3)) (PreH9 : (retval_3 <= 1)) (PreH10 : ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) ))) (PreH11 : (0 <= out)) (PreH12 : (out < U64_MOD)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) ))) (PreH16 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH17 : (x3 < U64_MOD)) (PreH18 : (0 <= x3)) (PreH19 : (x2 < U64_MOD)) (PreH20 : (0 <= x2)) (PreH21 : (x1 < U64_MOD)) (PreH22 : (0 <= x1)) (PreH23 : (x0 < U64_MOD)) (PreH24 : (0 <= x0)) (PreH25 : (A_non_alias < SM2_P_Z)) (PreH26 : (0 <= A_non_alias)) (PreH27 : (result_pre <> a_pre)) (PreH28 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &(( &( "tmp" ) )->ₛ "v") 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0)) ” 
  &&  “ ((Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0) < U64_MOD) ” 
  &&  “ (0 <= (Znth 3 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) 0)) ” 
  &&  “ (0 <= out_3) ” 
  &&  “ (out_3 < U64_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((((Znth 2 (replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))) 0) + (Znth 2 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_3 ) = (out_3 + (retval * U64_MOD ) )) ” 
  &&  “ (0 <= out_2) ” 
  &&  “ (out_2 < U64_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((((Znth 1 (replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) 0) + (Znth 1 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + retval_2 ) = (out_2 + (retval_3 * U64_MOD ) )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out < U64_MOD) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ ((((Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) + (Znth 0 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) 0) ) + 0 ) = (out + (retval_2 * U64_MOD ) )) ” 
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) <> 0) ”
  &&  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "tmp" ) )->ₛ "v") 3 0 4 (replace_Znth (2) (out_3) ((replace_Znth (1) (out_2) ((replace_Znth (0) (out) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))))))) )
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((a_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
.

Definition div_by_2_mod_p_partial_solve_wit_28_non_alias := div_by_2_mod_p_partial_solve_wit_28_non_alias_pure -> div_by_2_mod_p_partial_solve_wit_28_non_alias_aux.

Definition div_by_2_mod_p_partial_solve_wit_29_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_30_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_31_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_32_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C <> 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C <> 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_33_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_34_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_35_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_36_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_37_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_38_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") 1 4 )
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_39_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_40_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_41_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_42_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (T: Z) (C: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (T = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (A_non_alias < SM2_P_Z)) (PreH20 : (0 <= A_non_alias)) (PreH21 : (0 <= T)) (PreH22 : (T < U256_MOD)) (PreH23 : (0 <= C)) (PreH24 : (C <= 1)) (PreH25 : ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) ))) (PreH26 : (C = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
|--
  “ (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (T = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
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
  &&  “ (0 <= T) ” 
  &&  “ (T < U256_MOD) ” 
  &&  “ (0 <= C) ” 
  &&  “ (C <= 1) ” 
  &&  “ ((fp_div2_adjusted (A_non_alias)) = (T + (C * U256_MOD ) )) ” 
  &&  “ (C = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x2 1) (unsigned_last_nbits ((Z.shiftl x3 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x1 1) (unsigned_last_nbits ((Z.shiftl x2 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr x0 1) (unsigned_last_nbits ((Z.shiftl x1 63)) (64))))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_p )
.

Definition div_by_2_mod_p_partial_solve_wit_43_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_in_place < SM2_P_Z)) (PreH11 : (0 <= A_in_place)) (PreH12 : (result_pre = a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
|--
  “ (A_in_place = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (A_in_place < SM2_P_Z) ” 
  &&  “ (0 <= A_in_place) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_partial_solve_wit_44_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (A_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (A_non_alias < SM2_P_Z)) (PreH11 : (0 <= A_non_alias)) (PreH12 : (result_pre <> a_pre)) (PreH13 : ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0)) ,
  (UInt64Array.undef_seg &((result_pre)  # "u32" ->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
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
  &&  “ (result_pre <> a_pre) ” 
  &&  “ ((Z.land (Znth 0 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) 0) 1) = 0) ”
  &&  (((&((result_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &((result_pre)  # "u32" ->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&((result_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (Z.shiftr (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 1) (unsigned_last_nbits ((Z.shiftl (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)) 63)) (64))))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&((a_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Znth (3) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Znth (2) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Znth (1) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
  **  (((&(( &( "tmp" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Znth (0) ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z)))))))))) (0)))
.

Definition div_by_2_mod_p_derive_mont_non_alias_by_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_mont_non_alias: Z) ,
  “ (result_pre <> a_pre) ” 
  &&  “ (0 <= A_mont_non_alias) ” 
  &&  “ (A_mont_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
EX (A_non_alias: Z) ,
  (“ (result_pre <> a_pre) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  **
  (((store_fp a_pre A_non_alias )
  **  (store_fp result_pre (fp_div2 (A_non_alias)) )
  **  (store_sm2_p ))
  -*
  ((store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (store_fp result_pre (mont_p ((fp_div2 (A_mont_non_alias)))) )
  **  (store_sm2_p )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include u32_alias_Strategy_Correct.

Axiom proof_of_div_by_2_mod_p_safety_wit_1_in_place : div_by_2_mod_p_safety_wit_1_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_2_non_alias : div_by_2_mod_p_safety_wit_2_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_3_in_place : div_by_2_mod_p_safety_wit_3_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_4_non_alias : div_by_2_mod_p_safety_wit_4_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_5_in_place : div_by_2_mod_p_safety_wit_5_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_6_non_alias : div_by_2_mod_p_safety_wit_6_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_7_in_place : div_by_2_mod_p_safety_wit_7_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_8_in_place : div_by_2_mod_p_safety_wit_8_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_9_in_place : div_by_2_mod_p_safety_wit_9_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_10_non_alias : div_by_2_mod_p_safety_wit_10_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_11_non_alias : div_by_2_mod_p_safety_wit_11_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_12_non_alias : div_by_2_mod_p_safety_wit_12_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_13_in_place : div_by_2_mod_p_safety_wit_13_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_14_in_place : div_by_2_mod_p_safety_wit_14_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_15_in_place : div_by_2_mod_p_safety_wit_15_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_16_non_alias : div_by_2_mod_p_safety_wit_16_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_17_non_alias : div_by_2_mod_p_safety_wit_17_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_18_non_alias : div_by_2_mod_p_safety_wit_18_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_19_in_place : div_by_2_mod_p_safety_wit_19_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_20_in_place : div_by_2_mod_p_safety_wit_20_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_21_in_place : div_by_2_mod_p_safety_wit_21_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_22_non_alias : div_by_2_mod_p_safety_wit_22_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_23_non_alias : div_by_2_mod_p_safety_wit_23_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_24_non_alias : div_by_2_mod_p_safety_wit_24_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_25_in_place : div_by_2_mod_p_safety_wit_25_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_26_in_place : div_by_2_mod_p_safety_wit_26_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_27_in_place : div_by_2_mod_p_safety_wit_27_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_28_non_alias : div_by_2_mod_p_safety_wit_28_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_29_non_alias : div_by_2_mod_p_safety_wit_29_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_30_non_alias : div_by_2_mod_p_safety_wit_30_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_31_in_place : div_by_2_mod_p_safety_wit_31_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_32_non_alias : div_by_2_mod_p_safety_wit_32_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_33_in_place : div_by_2_mod_p_safety_wit_33_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_34_in_place : div_by_2_mod_p_safety_wit_34_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_35_in_place : div_by_2_mod_p_safety_wit_35_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_36_in_place : div_by_2_mod_p_safety_wit_36_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_37_in_place : div_by_2_mod_p_safety_wit_37_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_38_in_place : div_by_2_mod_p_safety_wit_38_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_39_non_alias : div_by_2_mod_p_safety_wit_39_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_40_non_alias : div_by_2_mod_p_safety_wit_40_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_41_non_alias : div_by_2_mod_p_safety_wit_41_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_42_non_alias : div_by_2_mod_p_safety_wit_42_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_43_non_alias : div_by_2_mod_p_safety_wit_43_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_44_non_alias : div_by_2_mod_p_safety_wit_44_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_45_in_place : div_by_2_mod_p_safety_wit_45_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_46_non_alias : div_by_2_mod_p_safety_wit_46_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_47_in_place : div_by_2_mod_p_safety_wit_47_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_48_in_place : div_by_2_mod_p_safety_wit_48_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_49_in_place : div_by_2_mod_p_safety_wit_49_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_50_in_place : div_by_2_mod_p_safety_wit_50_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_51_in_place : div_by_2_mod_p_safety_wit_51_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_52_in_place : div_by_2_mod_p_safety_wit_52_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_53_non_alias : div_by_2_mod_p_safety_wit_53_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_54_non_alias : div_by_2_mod_p_safety_wit_54_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_55_non_alias : div_by_2_mod_p_safety_wit_55_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_56_non_alias : div_by_2_mod_p_safety_wit_56_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_57_non_alias : div_by_2_mod_p_safety_wit_57_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_58_non_alias : div_by_2_mod_p_safety_wit_58_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_59_in_place : div_by_2_mod_p_safety_wit_59_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_60_non_alias : div_by_2_mod_p_safety_wit_60_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_61_in_place : div_by_2_mod_p_safety_wit_61_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_62_in_place : div_by_2_mod_p_safety_wit_62_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_63_in_place : div_by_2_mod_p_safety_wit_63_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_64_in_place : div_by_2_mod_p_safety_wit_64_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_65_in_place : div_by_2_mod_p_safety_wit_65_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_66_in_place : div_by_2_mod_p_safety_wit_66_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_67_non_alias : div_by_2_mod_p_safety_wit_67_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_68_non_alias : div_by_2_mod_p_safety_wit_68_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_69_non_alias : div_by_2_mod_p_safety_wit_69_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_70_non_alias : div_by_2_mod_p_safety_wit_70_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_71_non_alias : div_by_2_mod_p_safety_wit_71_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_72_non_alias : div_by_2_mod_p_safety_wit_72_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_73_in_place : div_by_2_mod_p_safety_wit_73_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_74_non_alias : div_by_2_mod_p_safety_wit_74_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_75_in_place : div_by_2_mod_p_safety_wit_75_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_76_in_place : div_by_2_mod_p_safety_wit_76_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_77_in_place : div_by_2_mod_p_safety_wit_77_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_78_in_place : div_by_2_mod_p_safety_wit_78_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_79_in_place : div_by_2_mod_p_safety_wit_79_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_80_in_place : div_by_2_mod_p_safety_wit_80_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_81_non_alias : div_by_2_mod_p_safety_wit_81_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_82_non_alias : div_by_2_mod_p_safety_wit_82_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_83_non_alias : div_by_2_mod_p_safety_wit_83_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_84_non_alias : div_by_2_mod_p_safety_wit_84_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_85_non_alias : div_by_2_mod_p_safety_wit_85_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_86_non_alias : div_by_2_mod_p_safety_wit_86_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_87_in_place : div_by_2_mod_p_safety_wit_87_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_88_non_alias : div_by_2_mod_p_safety_wit_88_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_89_in_place : div_by_2_mod_p_safety_wit_89_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_90_non_alias : div_by_2_mod_p_safety_wit_90_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_91_in_place : div_by_2_mod_p_safety_wit_91_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_92_in_place : div_by_2_mod_p_safety_wit_92_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_93_in_place : div_by_2_mod_p_safety_wit_93_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_94_in_place : div_by_2_mod_p_safety_wit_94_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_95_in_place : div_by_2_mod_p_safety_wit_95_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_96_in_place : div_by_2_mod_p_safety_wit_96_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_97_non_alias : div_by_2_mod_p_safety_wit_97_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_98_non_alias : div_by_2_mod_p_safety_wit_98_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_99_non_alias : div_by_2_mod_p_safety_wit_99_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_100_non_alias : div_by_2_mod_p_safety_wit_100_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_101_non_alias : div_by_2_mod_p_safety_wit_101_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_102_non_alias : div_by_2_mod_p_safety_wit_102_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_103_in_place : div_by_2_mod_p_safety_wit_103_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_104_in_place : div_by_2_mod_p_safety_wit_104_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_105_in_place : div_by_2_mod_p_safety_wit_105_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_106_in_place : div_by_2_mod_p_safety_wit_106_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_107_in_place : div_by_2_mod_p_safety_wit_107_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_108_in_place : div_by_2_mod_p_safety_wit_108_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_109_non_alias : div_by_2_mod_p_safety_wit_109_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_110_non_alias : div_by_2_mod_p_safety_wit_110_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_111_non_alias : div_by_2_mod_p_safety_wit_111_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_112_non_alias : div_by_2_mod_p_safety_wit_112_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_113_non_alias : div_by_2_mod_p_safety_wit_113_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_114_non_alias : div_by_2_mod_p_safety_wit_114_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_115_in_place : div_by_2_mod_p_safety_wit_115_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_116_non_alias : div_by_2_mod_p_safety_wit_116_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_117_in_place : div_by_2_mod_p_safety_wit_117_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_118_non_alias : div_by_2_mod_p_safety_wit_118_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_119_in_place : div_by_2_mod_p_safety_wit_119_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_120_in_place : div_by_2_mod_p_safety_wit_120_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_121_in_place : div_by_2_mod_p_safety_wit_121_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_122_in_place : div_by_2_mod_p_safety_wit_122_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_123_in_place : div_by_2_mod_p_safety_wit_123_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_124_in_place : div_by_2_mod_p_safety_wit_124_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_125_non_alias : div_by_2_mod_p_safety_wit_125_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_126_non_alias : div_by_2_mod_p_safety_wit_126_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_127_non_alias : div_by_2_mod_p_safety_wit_127_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_128_non_alias : div_by_2_mod_p_safety_wit_128_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_129_non_alias : div_by_2_mod_p_safety_wit_129_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_130_non_alias : div_by_2_mod_p_safety_wit_130_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_131_in_place : div_by_2_mod_p_safety_wit_131_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_132_in_place : div_by_2_mod_p_safety_wit_132_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_133_in_place : div_by_2_mod_p_safety_wit_133_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_134_in_place : div_by_2_mod_p_safety_wit_134_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_135_in_place : div_by_2_mod_p_safety_wit_135_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_136_in_place : div_by_2_mod_p_safety_wit_136_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_137_non_alias : div_by_2_mod_p_safety_wit_137_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_138_non_alias : div_by_2_mod_p_safety_wit_138_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_139_non_alias : div_by_2_mod_p_safety_wit_139_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_140_non_alias : div_by_2_mod_p_safety_wit_140_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_141_non_alias : div_by_2_mod_p_safety_wit_141_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_142_non_alias : div_by_2_mod_p_safety_wit_142_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_143_in_place : div_by_2_mod_p_safety_wit_143_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_144_non_alias : div_by_2_mod_p_safety_wit_144_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_145_in_place : div_by_2_mod_p_safety_wit_145_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_146_non_alias : div_by_2_mod_p_safety_wit_146_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_147_in_place : div_by_2_mod_p_safety_wit_147_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_148_in_place : div_by_2_mod_p_safety_wit_148_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_149_in_place : div_by_2_mod_p_safety_wit_149_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_150_in_place : div_by_2_mod_p_safety_wit_150_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_151_in_place : div_by_2_mod_p_safety_wit_151_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_152_in_place : div_by_2_mod_p_safety_wit_152_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_153_non_alias : div_by_2_mod_p_safety_wit_153_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_154_non_alias : div_by_2_mod_p_safety_wit_154_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_155_non_alias : div_by_2_mod_p_safety_wit_155_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_156_non_alias : div_by_2_mod_p_safety_wit_156_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_157_non_alias : div_by_2_mod_p_safety_wit_157_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_158_non_alias : div_by_2_mod_p_safety_wit_158_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_159_in_place : div_by_2_mod_p_safety_wit_159_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_160_in_place : div_by_2_mod_p_safety_wit_160_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_161_in_place : div_by_2_mod_p_safety_wit_161_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_162_in_place : div_by_2_mod_p_safety_wit_162_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_163_in_place : div_by_2_mod_p_safety_wit_163_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_164_in_place : div_by_2_mod_p_safety_wit_164_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_165_non_alias : div_by_2_mod_p_safety_wit_165_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_166_non_alias : div_by_2_mod_p_safety_wit_166_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_167_non_alias : div_by_2_mod_p_safety_wit_167_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_168_non_alias : div_by_2_mod_p_safety_wit_168_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_169_non_alias : div_by_2_mod_p_safety_wit_169_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_170_non_alias : div_by_2_mod_p_safety_wit_170_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_171_in_place : div_by_2_mod_p_safety_wit_171_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_172_non_alias : div_by_2_mod_p_safety_wit_172_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_173_in_place : div_by_2_mod_p_safety_wit_173_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_174_non_alias : div_by_2_mod_p_safety_wit_174_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_175_in_place : div_by_2_mod_p_safety_wit_175_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_176_in_place : div_by_2_mod_p_safety_wit_176_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_177_in_place : div_by_2_mod_p_safety_wit_177_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_178_non_alias : div_by_2_mod_p_safety_wit_178_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_179_non_alias : div_by_2_mod_p_safety_wit_179_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_180_non_alias : div_by_2_mod_p_safety_wit_180_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_181_in_place : div_by_2_mod_p_safety_wit_181_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_182_in_place : div_by_2_mod_p_safety_wit_182_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_183_in_place : div_by_2_mod_p_safety_wit_183_in_place.
Axiom proof_of_div_by_2_mod_p_safety_wit_184_non_alias : div_by_2_mod_p_safety_wit_184_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_185_non_alias : div_by_2_mod_p_safety_wit_185_non_alias.
Axiom proof_of_div_by_2_mod_p_safety_wit_186_non_alias : div_by_2_mod_p_safety_wit_186_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_1_1_non_alias : div_by_2_mod_p_entail_wit_1_1_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_1_2_in_place : div_by_2_mod_p_entail_wit_1_2_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_2_1_non_alias : div_by_2_mod_p_entail_wit_2_1_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_2_2_in_place : div_by_2_mod_p_entail_wit_2_2_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_3_1_non_alias : div_by_2_mod_p_entail_wit_3_1_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_3_2_in_place : div_by_2_mod_p_entail_wit_3_2_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_4_non_alias : div_by_2_mod_p_entail_wit_4_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_5_in_place : div_by_2_mod_p_entail_wit_5_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_6_1_in_place : div_by_2_mod_p_entail_wit_6_1_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_6_2_non_alias : div_by_2_mod_p_entail_wit_6_2_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_7_1_in_place : div_by_2_mod_p_entail_wit_7_1_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_7_2_non_alias : div_by_2_mod_p_entail_wit_7_2_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_8_1_in_place : div_by_2_mod_p_entail_wit_8_1_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_8_2_non_alias : div_by_2_mod_p_entail_wit_8_2_non_alias.
Axiom proof_of_div_by_2_mod_p_entail_wit_8_3_in_place : div_by_2_mod_p_entail_wit_8_3_in_place.
Axiom proof_of_div_by_2_mod_p_entail_wit_8_4_non_alias : div_by_2_mod_p_entail_wit_8_4_non_alias.
Axiom proof_of_div_by_2_mod_p_return_wit_1_in_place : div_by_2_mod_p_return_wit_1_in_place.
Axiom proof_of_div_by_2_mod_p_return_wit_2_non_alias : div_by_2_mod_p_return_wit_2_non_alias.
Axiom proof_of_div_by_2_mod_p_return_wit_3_in_place : div_by_2_mod_p_return_wit_3_in_place.
Axiom proof_of_div_by_2_mod_p_return_wit_4_non_alias : div_by_2_mod_p_return_wit_4_non_alias.
Axiom proof_of_div_by_2_mod_p_return_wit_5_in_place : div_by_2_mod_p_return_wit_5_in_place.
Axiom proof_of_div_by_2_mod_p_return_wit_6_non_alias : div_by_2_mod_p_return_wit_6_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_1_non_alias : div_by_2_mod_p_partial_solve_wit_1_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_2_in_place : div_by_2_mod_p_partial_solve_wit_2_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_3_in_place : div_by_2_mod_p_partial_solve_wit_3_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_4_non_alias : div_by_2_mod_p_partial_solve_wit_4_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_5_in_place : div_by_2_mod_p_partial_solve_wit_5_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_6_in_place : div_by_2_mod_p_partial_solve_wit_6_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_7_in_place_pure : div_by_2_mod_p_partial_solve_wit_7_in_place_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_7_in_place : div_by_2_mod_p_partial_solve_wit_7_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_8_non_alias : div_by_2_mod_p_partial_solve_wit_8_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_9_non_alias : div_by_2_mod_p_partial_solve_wit_9_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_10_non_alias_pure : div_by_2_mod_p_partial_solve_wit_10_non_alias_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_10_non_alias : div_by_2_mod_p_partial_solve_wit_10_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_11_in_place : div_by_2_mod_p_partial_solve_wit_11_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_12_in_place : div_by_2_mod_p_partial_solve_wit_12_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place_pure : div_by_2_mod_p_partial_solve_wit_13_in_place_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_13_in_place : div_by_2_mod_p_partial_solve_wit_13_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_14_non_alias : div_by_2_mod_p_partial_solve_wit_14_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_15_non_alias : div_by_2_mod_p_partial_solve_wit_15_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias_pure : div_by_2_mod_p_partial_solve_wit_16_non_alias_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_16_non_alias : div_by_2_mod_p_partial_solve_wit_16_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_17_in_place : div_by_2_mod_p_partial_solve_wit_17_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_18_in_place : div_by_2_mod_p_partial_solve_wit_18_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place_pure : div_by_2_mod_p_partial_solve_wit_19_in_place_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_19_in_place : div_by_2_mod_p_partial_solve_wit_19_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_20_non_alias : div_by_2_mod_p_partial_solve_wit_20_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_21_non_alias : div_by_2_mod_p_partial_solve_wit_21_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias_pure : div_by_2_mod_p_partial_solve_wit_22_non_alias_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_22_non_alias : div_by_2_mod_p_partial_solve_wit_22_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_23_in_place : div_by_2_mod_p_partial_solve_wit_23_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_24_in_place : div_by_2_mod_p_partial_solve_wit_24_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place_pure : div_by_2_mod_p_partial_solve_wit_25_in_place_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_25_in_place : div_by_2_mod_p_partial_solve_wit_25_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_26_non_alias : div_by_2_mod_p_partial_solve_wit_26_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_27_non_alias : div_by_2_mod_p_partial_solve_wit_27_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias_pure : div_by_2_mod_p_partial_solve_wit_28_non_alias_pure.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_28_non_alias : div_by_2_mod_p_partial_solve_wit_28_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_29_non_alias : div_by_2_mod_p_partial_solve_wit_29_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_30_non_alias : div_by_2_mod_p_partial_solve_wit_30_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_31_non_alias : div_by_2_mod_p_partial_solve_wit_31_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_32_non_alias : div_by_2_mod_p_partial_solve_wit_32_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_33_non_alias : div_by_2_mod_p_partial_solve_wit_33_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_34_in_place : div_by_2_mod_p_partial_solve_wit_34_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_35_non_alias : div_by_2_mod_p_partial_solve_wit_35_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_36_non_alias : div_by_2_mod_p_partial_solve_wit_36_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_37_in_place : div_by_2_mod_p_partial_solve_wit_37_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_38_non_alias : div_by_2_mod_p_partial_solve_wit_38_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_39_non_alias : div_by_2_mod_p_partial_solve_wit_39_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_40_in_place : div_by_2_mod_p_partial_solve_wit_40_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_41_non_alias : div_by_2_mod_p_partial_solve_wit_41_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_42_non_alias : div_by_2_mod_p_partial_solve_wit_42_non_alias.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_43_in_place : div_by_2_mod_p_partial_solve_wit_43_in_place.
Axiom proof_of_div_by_2_mod_p_partial_solve_wit_44_non_alias : div_by_2_mod_p_partial_solve_wit_44_non_alias.
Axiom proof_of_div_by_2_mod_p_derive_mont_non_alias_by_non_alias : div_by_2_mod_p_derive_mont_non_alias_by_non_alias.

End VC_Correct.
