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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.

(*----- Function CopyJPoint -----*)

Definition CopyJPoint_return_wit_1_non_alias := 
forall (dst_pre: Z) (src_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = dst_pre)) ,
  (store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_jpoint_fields dst_pre X_non_alias Y_non_alias Z_non_alias )
|--
  (store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_jpoint_fields dst_pre X_non_alias Y_non_alias Z_non_alias )
.

Definition CopyJPoint_return_wit_2_in_place := 
forall (dst_pre: Z) (src_pre: Z) (Z_in_place: Z) (Y_in_place: Z) (X_in_place: Z) (retval: Z) (PreH1 : (retval = dst_pre)) (PreH2 : (dst_pre = src_pre)) (PreH3 : (dst_pre = src_pre)) ,
  (store_jpoint_fields dst_pre X_in_place Y_in_place Z_in_place )
|--
  “ (dst_pre = src_pre) ”
  &&  (store_jpoint_fields dst_pre X_in_place Y_in_place Z_in_place )
.

Definition CopyJPoint_partial_solve_wit_1_non_alias_pure := 
forall (dst_pre: Z) (src_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ”
.

Definition CopyJPoint_partial_solve_wit_1_non_alias_aux := 
forall (dst_pre: Z) (src_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  (store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ”
  &&  (store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition CopyJPoint_partial_solve_wit_1_non_alias := CopyJPoint_partial_solve_wit_1_non_alias_pure -> CopyJPoint_partial_solve_wit_1_non_alias_aux.

Definition CopyJPoint_partial_solve_wit_2_in_place_pure := 
forall (dst_pre: Z) (src_pre: Z) (Z_in_place: Z) (Y_in_place: Z) (X_in_place: Z) (PreH1 : (dst_pre = src_pre)) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (store_jpoint_fields src_pre X_in_place Y_in_place Z_in_place )
|--
  “ (dst_pre = src_pre) ” 
  &&  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ”
.

Definition CopyJPoint_partial_solve_wit_2_in_place_aux := 
forall (dst_pre: Z) (src_pre: Z) (Z_in_place: Z) (Y_in_place: Z) (X_in_place: Z) (PreH1 : (dst_pre = src_pre)) ,
  (store_jpoint_fields src_pre X_in_place Y_in_place Z_in_place )
|--
  “ (dst_pre = src_pre) ” 
  &&  “ (sizeof( "JPoint" ) = sizeof( "JPoint" )) ” 
  &&  “ (dst_pre = src_pre) ”
  &&  (store_jpoint_fields src_pre X_in_place Y_in_place Z_in_place )
.

Definition CopyJPoint_partial_solve_wit_2_in_place := CopyJPoint_partial_solve_wit_2_in_place_pure -> CopyJPoint_partial_solve_wit_2_in_place_aux.

Definition CopyJPoint_derive_mont_in_place_by_in_place := 
forall (dst_pre: Z) (src_pre: Z) (P_mont_in_place: ec_point) ,
  “ (dst_pre = src_pre) ”
  &&  (store_mont_jpoint src_pre P_mont_in_place )
|--
EX (X_in_place: Z) (Y_in_place: Z) (Z_in_place: Z) ,
  (“ (dst_pre = src_pre) ”
  &&  (store_jpoint_fields src_pre X_in_place Y_in_place Z_in_place ))
  **
  ((“ (dst_pre = src_pre) ”
  &&  (store_jpoint_fields dst_pre X_in_place Y_in_place Z_in_place ))
  -*
  (“ (dst_pre = src_pre) ”
  &&  (store_mont_jpoint dst_pre P_mont_in_place )))
.

Definition CopyJPoint_derive_mont_non_alias_by_non_alias := 
forall (dst_pre: Z) (src_pre: Z) (P_mont_non_alias: ec_point) ,
  (store_mont_jpoint src_pre P_mont_non_alias )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) (Z_non_alias: Z) ,
  ((store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((dst_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
  **
  (((store_jpoint_fields src_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_jpoint_fields dst_pre X_non_alias Y_non_alias Z_non_alias ))
  -*
  ((store_mont_jpoint src_pre P_mont_non_alias )
  **  (store_mont_jpoint dst_pre P_mont_non_alias )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include ecc_representation_Strategy_Correct.

Axiom proof_of_CopyJPoint_return_wit_1_non_alias : CopyJPoint_return_wit_1_non_alias.
Axiom proof_of_CopyJPoint_return_wit_2_in_place : CopyJPoint_return_wit_2_in_place.
Axiom proof_of_CopyJPoint_partial_solve_wit_1_non_alias_pure : CopyJPoint_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_CopyJPoint_partial_solve_wit_1_non_alias : CopyJPoint_partial_solve_wit_1_non_alias.
Axiom proof_of_CopyJPoint_partial_solve_wit_2_in_place_pure : CopyJPoint_partial_solve_wit_2_in_place_pure.
Axiom proof_of_CopyJPoint_partial_solve_wit_2_in_place : CopyJPoint_partial_solve_wit_2_in_place.
Axiom proof_of_CopyJPoint_derive_mont_in_place_by_in_place : CopyJPoint_derive_mont_in_place_by_in_place.
Axiom proof_of_CopyJPoint_derive_mont_non_alias_by_non_alias : CopyJPoint_derive_mont_non_alias_by_non_alias.

End VC_Correct.
