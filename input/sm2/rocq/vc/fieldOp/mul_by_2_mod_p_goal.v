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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function mul_by_2_mod_p -----*)

Definition mul_by_2_mod_p_return_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((2 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
|--
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((2 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
.

Definition mul_by_2_mod_p_partial_solve_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
.

Definition mul_by_2_mod_p_derive_mont_non_alias_by_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_mont_non_alias: Z) ,
  “ (0 <= A_mont_non_alias) ” 
  &&  “ (A_mont_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
|--
EX (A_non_alias: Z) ,
  ((store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p ))
  **
  (((store_fp a_pre A_non_alias )
  **  (store_fp result_pre (Zmod ((2 * A_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p ))
  -*
  ((store_fp a_pre (mont_p (A_mont_non_alias)) )
  **  (store_fp result_pre (mont_p ((2 * A_mont_non_alias ))) )
  **  (store_sm2_p )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_mul_by_2_mod_p_return_wit_1 : mul_by_2_mod_p_return_wit_1.
Axiom proof_of_mul_by_2_mod_p_partial_solve_wit_1 : mul_by_2_mod_p_partial_solve_wit_1.
Axiom proof_of_mul_by_2_mod_p_derive_mont_non_alias_by_non_alias : mul_by_2_mod_p_derive_mont_non_alias_by_non_alias.

End VC_Correct.
