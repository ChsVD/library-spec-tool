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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function montg_mul_mod_p -----*)

Definition montg_mul_mod_p_return_wit_1_non_alias := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((A_non_alias * B_non_alias ) + (K_2 * SM2_P_Z ) ))) ,
  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_non_alias * B_non_alias ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (B_non_alias: Z) (A_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((A_non_alias * B_non_alias ) + (K_2 * SM2_P_Z ) ))) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ ((Zout_2 * U256_MOD ) = ((A_non_alias * B_non_alias ) + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition montg_mul_mod_p_return_wit_2_r_eq_a := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= Zout_2)) (PreH3 : (Zout_2 < SM2_P_Z)) (PreH4 : ((Zout_2 * U256_MOD ) = ((A_r_eq_a * B_r_eq_a ) + (K_2 * SM2_P_Z ) ))) (PreH5 : (result_pre = a_pre)) ,
  (store_fp result_pre Zout_2 )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_r_eq_a * B_r_eq_a ) + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Zout )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= Zout_2)) (PreH3 : (Zout_2 < SM2_P_Z)) (PreH4 : ((Zout_2 * U256_MOD ) = ((A_r_eq_a * B_r_eq_a ) + (K_2 * SM2_P_Z ) ))) (PreH5 : (result_pre = a_pre)) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ (a_pre = a_pre) ” 
  &&  “ ((Zout_2 * U256_MOD ) = ((A_r_eq_a * B_r_eq_a ) + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition montg_mul_mod_p_return_wit_3_r_eq_b := 
(
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (result_pre = b_pre)) (PreH2 : (0 <= Zout_2)) (PreH3 : (Zout_2 < SM2_P_Z)) (PreH4 : ((Zout_2 * U256_MOD ) = ((A_r_eq_b * B_r_eq_b ) + (K_2 * SM2_P_Z ) ))) (PreH5 : (result_pre = b_pre)) ,
  (store_u256 a_pre A_r_eq_b )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (result_pre = b_pre) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_r_eq_b * B_r_eq_b ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_r_eq_b )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (b_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (result_pre = b_pre)) (PreH2 : (0 <= Zout_2)) (PreH3 : (Zout_2 < SM2_P_Z)) (PreH4 : ((Zout_2 * U256_MOD ) = ((A_r_eq_b * B_r_eq_b ) + (K_2 * SM2_P_Z ) ))) (PreH5 : (result_pre = b_pre)) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ (b_pre = b_pre) ” 
  &&  “ ((Zout_2 * U256_MOD ) = ((A_r_eq_b * B_r_eq_b ) + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition montg_mul_mod_p_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_non_alias: Z) (A_non_alias: Z) ,
  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_mul_mod_p_partial_solve_wit_2_r_eq_a_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_r_eq_a )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ”
.

Definition montg_mul_mod_p_partial_solve_wit_2_r_eq_a_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_a: Z) (A_r_eq_a: Z) (PreH1 : (result_pre = a_pre)) ,
  (store_u256 a_pre A_r_eq_a )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_r_eq_a )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_mul_mod_p_partial_solve_wit_2_r_eq_a := montg_mul_mod_p_partial_solve_wit_2_r_eq_a_pure -> montg_mul_mod_p_partial_solve_wit_2_r_eq_a_aux.

Definition montg_mul_mod_p_partial_solve_wit_3_r_eq_b_pure := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = b_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_r_eq_b )
  **  (store_u256 b_pre B_r_eq_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = b_pre) ”
.

Definition montg_mul_mod_p_partial_solve_wit_3_r_eq_b_aux := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_r_eq_b: Z) (A_r_eq_b: Z) (PreH1 : (result_pre = b_pre)) ,
  (store_u256 a_pre A_r_eq_b )
  **  (store_u256 b_pre B_r_eq_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = b_pre) ” 
  &&  “ (result_pre = b_pre) ”
  &&  (store_u256 a_pre A_r_eq_b )
  **  (store_u256 b_pre B_r_eq_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_mul_mod_p_partial_solve_wit_3_r_eq_b := montg_mul_mod_p_partial_solve_wit_3_r_eq_b_pure -> montg_mul_mod_p_partial_solve_wit_3_r_eq_b_aux.

Definition montg_mul_mod_p_derive_mont_r_eq_b_by_r_eq_b := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_mont_r_eq_b: Z) (A_mont_r_eq_b: Z) ,
  “ (result_pre = b_pre) ” 
  &&  “ (0 <= A_mont_r_eq_b) ” 
  &&  “ (A_mont_r_eq_b < SM2_P_Z) ” 
  &&  “ (0 <= B_mont_r_eq_b) ” 
  &&  “ (B_mont_r_eq_b < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_r_eq_b)) )
  **  (store_fp b_pre (mont_p (B_mont_r_eq_b)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_r_eq_b: Z) (B_r_eq_b: Z) ,
  (“ (result_pre = b_pre) ”
  &&  (store_u256 a_pre A_r_eq_b )
  **  (store_u256 b_pre B_r_eq_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Zout,
  “ (result_pre = b_pre) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_r_eq_b * B_r_eq_b ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_r_eq_b )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (“ (result_pre = b_pre) ”
  &&  (store_fp a_pre (mont_p (A_mont_r_eq_b)) )
  **  (store_fp result_pre (mont_p ((A_mont_r_eq_b * B_mont_r_eq_b ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Definition montg_mul_mod_p_derive_mont_r_eq_a_by_r_eq_a := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_mont_r_eq_a: Z) (A_mont_r_eq_a: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_mont_r_eq_a) ” 
  &&  “ (A_mont_r_eq_a < SM2_P_Z) ” 
  &&  “ (0 <= B_mont_r_eq_a) ” 
  &&  “ (B_mont_r_eq_a < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_r_eq_a)) )
  **  (store_fp b_pre (mont_p (B_mont_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_r_eq_a: Z) (B_r_eq_a: Z) ,
  (“ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_r_eq_a )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Zout,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_r_eq_a * B_r_eq_a ) + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Zout )
  **  (store_u256 b_pre B_r_eq_a )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (“ (result_pre = a_pre) ”
  &&  (store_fp result_pre (mont_p ((A_mont_r_eq_a * B_mont_r_eq_a ))) )
  **  (store_fp b_pre (mont_p (B_mont_r_eq_a)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Definition montg_mul_mod_p_derive_mont_non_alias_by_non_alias := 
forall (result_pre: Z) (b_pre: Z) (a_pre: Z) (B_mont_non_alias: Z) (A_mont_non_alias: Z) ,
  “ (0 <= A_mont_non_alias) ” 
  &&  “ (A_mont_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= B_mont_non_alias) ” 
  &&  “ (B_mont_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (store_fp b_pre (mont_p (B_mont_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_non_alias: Z) (B_non_alias: Z) ,
  ((store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Zout,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_non_alias * B_non_alias ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_u256 b_pre B_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  ((store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (store_fp b_pre (mont_p (B_mont_non_alias)) )
  **  (store_fp result_pre (mont_p ((A_mont_non_alias * B_mont_non_alias ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_montg_mul_mod_p_return_wit_1_non_alias : montg_mul_mod_p_return_wit_1_non_alias.
Axiom proof_of_montg_mul_mod_p_return_wit_2_r_eq_a : montg_mul_mod_p_return_wit_2_r_eq_a.
Axiom proof_of_montg_mul_mod_p_return_wit_3_r_eq_b : montg_mul_mod_p_return_wit_3_r_eq_b.
Axiom proof_of_montg_mul_mod_p_partial_solve_wit_1_non_alias : montg_mul_mod_p_partial_solve_wit_1_non_alias.
Axiom proof_of_montg_mul_mod_p_partial_solve_wit_2_r_eq_a_pure : montg_mul_mod_p_partial_solve_wit_2_r_eq_a_pure.
Axiom proof_of_montg_mul_mod_p_partial_solve_wit_2_r_eq_a : montg_mul_mod_p_partial_solve_wit_2_r_eq_a.
Axiom proof_of_montg_mul_mod_p_partial_solve_wit_3_r_eq_b_pure : montg_mul_mod_p_partial_solve_wit_3_r_eq_b_pure.
Axiom proof_of_montg_mul_mod_p_partial_solve_wit_3_r_eq_b : montg_mul_mod_p_partial_solve_wit_3_r_eq_b.
Axiom proof_of_montg_mul_mod_p_derive_mont_r_eq_b_by_r_eq_b : montg_mul_mod_p_derive_mont_r_eq_b_by_r_eq_b.
Axiom proof_of_montg_mul_mod_p_derive_mont_r_eq_a_by_r_eq_a : montg_mul_mod_p_derive_mont_r_eq_a_by_r_eq_a.
Axiom proof_of_montg_mul_mod_p_derive_mont_non_alias_by_non_alias : montg_mul_mod_p_derive_mont_non_alias_by_non_alias.

End VC_Correct.
