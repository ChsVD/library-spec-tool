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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.

(*----- Function copy_bignum -----*)

Definition copy_bignum_safety_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (X_raw: Z) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_u256_limbs src_pre X_raw )
  **  (UInt64Array.undef_full dst_pre 4 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition copy_bignum_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (X_raw: Z) (retval: Z) (PreH1 : (retval = dst_pre)) ,
  (store_u256_limbs src_pre X_raw )
  **  (store_u256_limbs dst_pre X_raw )
|--
  (store_u256_limbs src_pre X_raw )
  **  (store_u256_limbs dst_pre X_raw )
.

Definition copy_bignum_partial_solve_wit_1_pure := 
forall (dst_pre: Z) (src_pre: Z) (X_raw: Z) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_u256_limbs src_pre X_raw )
  **  (UInt64Array.undef_full dst_pre 4 )
|--
  “ ((sizeof(UINT64) * 4 ) = 32) ”
.

Definition copy_bignum_partial_solve_wit_1_aux := 
forall (dst_pre: Z) (src_pre: Z) (X_raw: Z) ,
  (store_u256_limbs src_pre X_raw )
  **  (UInt64Array.undef_full dst_pre 4 )
|--
  “ ((sizeof(UINT64) * 4 ) = 32) ”
  &&  (store_u256_limbs src_pre X_raw )
  **  (UInt64Array.undef_full dst_pre 4 )
.

Definition copy_bignum_partial_solve_wit_1 := copy_bignum_partial_solve_wit_1_pure -> copy_bignum_partial_solve_wit_1_aux.

Definition copy_bignum_derive_field_non_alias_by_raw := 
forall (dst_pre: Z) (src_pre: Z) (PD_field_non_alias: Z) (PS_field_non_alias: Z) (X_field_non_alias: Z) ,
  “ (src_pre = PS_field_non_alias) ” 
  &&  “ (dst_pre = PD_field_non_alias) ” 
  &&  “ (0 <= X_field_non_alias) ” 
  &&  “ (X_field_non_alias < SM2_P_Z) ”
  &&  (store_fp PS_field_non_alias X_field_non_alias )
  **  (UInt64Array.undef_full dst_pre 4 )
|--
EX (X_raw: Z) ,
  ((store_u256_limbs src_pre X_raw )
  **  (UInt64Array.undef_full dst_pre 4 ))
  **
  (((store_u256_limbs src_pre X_raw )
  **  (store_u256_limbs dst_pre X_raw ))
  -*
  (“ (src_pre = PS_field_non_alias) ” 
  &&  “ (dst_pre = PD_field_non_alias) ”
  &&  (store_fp PS_field_non_alias X_field_non_alias )
  **  (store_fp PD_field_non_alias X_field_non_alias )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_copy_bignum_safety_wit_1 : copy_bignum_safety_wit_1.
Axiom proof_of_copy_bignum_return_wit_1 : copy_bignum_return_wit_1.
Axiom proof_of_copy_bignum_partial_solve_wit_1_pure : copy_bignum_partial_solve_wit_1_pure.
Axiom proof_of_copy_bignum_partial_solve_wit_1 : copy_bignum_partial_solve_wit_1.
Axiom proof_of_copy_bignum_derive_field_non_alias_by_raw : copy_bignum_derive_field_non_alias_by_raw.

End VC_Correct.
