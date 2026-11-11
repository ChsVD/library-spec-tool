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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import jpoint_double_trace_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import jpoint_double_trace_strategy_proof.

(*----- Function montg_double_jpoint -----*)

Definition montg_double_jpoint_entail_wit_1_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (r_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_mont_jpoint_coords a_pre JX_in_place JY_in_place JZ_in_place )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_jpoint_fields a_pre (mont_p (JX_in_place)) (mont_p (JY_in_place)) (mont_p (JZ_in_place)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_jpoint_fields a_pre (mont_p (JX_non_alias)) (mont_p (JY_non_alias)) (mont_p (JZ_non_alias)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_double_jpoint_entail_wit_1_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_mont_jpoint_coords a_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_jpoint_fields a_pre (mont_p (JX_in_place)) (mont_p (JY_in_place)) (mont_p (JZ_in_place)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_jpoint_fields a_pre (mont_p (JX_non_alias)) (mont_p (JY_non_alias)) (mont_p (JZ_non_alias)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_double_jpoint_entail_wit_2_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (JZ_in_place < SM2_P_Z)) (PreH2 : (0 <= JZ_in_place)) (PreH3 : (JY_in_place < SM2_P_Z)) (PreH4 : (0 <= JY_in_place)) (PreH5 : (JX_in_place < SM2_P_Z)) (PreH6 : (0 <= JX_in_place)) (PreH7 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH8 : (r_pre = a_pre)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  (store_jpoint_fields a_pre (mont_p (JX_in_place)) (mont_p (JY_in_place)) (mont_p (JZ_in_place)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (store_jpoint_fields a_pre (mont_p (JX_in_place)) (mont_p (JY_in_place)) (mont_p (JZ_in_place)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_double_jpoint_entail_wit_3_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (JZ_in_place < SM2_P_Z)) (PreH2 : (0 <= JZ_in_place)) (PreH3 : (JY_in_place < SM2_P_Z)) (PreH4 : (0 <= JY_in_place)) (PreH5 : (JX_in_place < SM2_P_Z)) (PreH6 : (0 <= JX_in_place)) (PreH7 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH8 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((JZ_in_place * JZ_in_place ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_3_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (JZ_non_alias < SM2_P_Z)) (PreH2 : (0 <= JZ_non_alias)) (PreH3 : (JY_non_alias < SM2_P_Z)) (PreH4 : (0 <= JY_non_alias)) (PreH5 : (JX_non_alias < SM2_P_Z)) (PreH6 : (0 <= JX_non_alias)) (PreH7 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((JZ_non_alias * JZ_non_alias ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_4_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (JY_in_place)))) (PreH3 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH5 : (JZ_in_place < SM2_P_Z)) (PreH6 : (0 <= JZ_in_place)) (PreH7 : (JY_in_place < SM2_P_Z)) (PreH8 : (0 <= JY_in_place)) (PreH9 : (JX_in_place < SM2_P_Z)) (PreH10 : (0 <= JX_in_place)) (PreH11 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH12 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((2 * JY_in_place ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_4_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH3 : (JZ_non_alias < SM2_P_Z)) (PreH4 : (0 <= JZ_non_alias)) (PreH5 : (JY_non_alias < SM2_P_Z)) (PreH6 : (0 <= JY_non_alias)) (PreH7 : (JX_non_alias < SM2_P_Z)) (PreH8 : (0 <= JX_non_alias)) (PreH9 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((2 * JY_non_alias ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_5_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH4 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (JY_in_place)))) (PreH6 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH8 : (JZ_in_place < SM2_P_Z)) (PreH9 : (0 <= JZ_in_place)) (PreH10 : (JY_in_place < SM2_P_Z)) (PreH11 : (0 <= JY_in_place)) (PreH12 : (JX_in_place < SM2_P_Z)) (PreH13 : (0 <= JX_in_place)) (PreH14 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH15 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_s2 (JY_in_place)) * (jdouble_trace_s2 (JY_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_5_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH4 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH6 : (JZ_non_alias < SM2_P_Z)) (PreH7 : (0 <= JZ_non_alias)) (PreH8 : (JY_non_alias < SM2_P_Z)) (PreH9 : (0 <= JY_non_alias)) (PreH10 : (JX_non_alias < SM2_P_Z)) (PreH11 : (0 <= JX_non_alias)) (PreH12 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_s2 (JY_non_alias)) * (jdouble_trace_s2 (JY_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_6_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (JX_in_place)))) (PreH3 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH5 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH7 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (JY_in_place)))) (PreH9 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH11 : (JZ_in_place < SM2_P_Z)) (PreH12 : (0 <= JZ_in_place)) (PreH13 : (JY_in_place < SM2_P_Z)) (PreH14 : (0 <= JY_in_place)) (PreH15 : (JX_in_place < SM2_P_Z)) (PreH16 : (0 <= JX_in_place)) (PreH17 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH18 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "U2" ) ) (mont_p (((jdouble_trace_m4 (JY_in_place)) * JX_in_place ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_6_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH3 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH5 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH7 : (JZ_non_alias < SM2_P_Z)) (PreH8 : (0 <= JZ_non_alias)) (PreH9 : (JY_non_alias < SM2_P_Z)) (PreH10 : (0 <= JY_non_alias)) (PreH11 : (JX_non_alias < SM2_P_Z)) (PreH12 : (0 <= JX_non_alias)) (PreH13 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "U2" ) ) (mont_p (((jdouble_trace_m4 (JY_non_alias)) * JX_non_alias ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_7_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH4 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (JX_in_place)))) (PreH6 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH8 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH10 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (JY_in_place)))) (PreH12 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH14 : (JZ_in_place < SM2_P_Z)) (PreH15 : (0 <= JZ_in_place)) (PreH16 : (JY_in_place < SM2_P_Z)) (PreH17 : (0 <= JY_in_place)) (PreH18 : (JX_in_place < SM2_P_Z)) (PreH19 : (0 <= JX_in_place)) (PreH20 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH21 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_m4 (JY_in_place)) * (jdouble_trace_m4 (JY_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_7_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH4 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH6 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH8 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH10 : (JZ_non_alias < SM2_P_Z)) (PreH11 : (0 <= JZ_non_alias)) (PreH12 : (JY_non_alias < SM2_P_Z)) (PreH13 : (0 <= JY_non_alias)) (PreH14 : (JX_non_alias < SM2_P_Z)) (PreH15 : (0 <= JX_non_alias)) (PreH16 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_m4 (JY_non_alias)) * (jdouble_trace_m4 (JY_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_8_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH3 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH5 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (JX_in_place)))) (PreH7 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH9 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH11 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (mont_p (JY_in_place)))) (PreH13 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH15 : (JZ_in_place < SM2_P_Z)) (PreH16 : (0 <= JZ_in_place)) (PreH17 : (JY_in_place < SM2_P_Z)) (PreH18 : (0 <= JY_in_place)) (PreH19 : (JX_in_place < SM2_P_Z)) (PreH20 : (0 <= JX_in_place)) (PreH21 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH22 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((fp_div2 ((jdouble_trace_t16 (JY_in_place)))))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_8_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH3 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH5 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH7 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH9 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH11 : (JZ_non_alias < SM2_P_Z)) (PreH12 : (0 <= JZ_non_alias)) (PreH13 : (JY_non_alias < SM2_P_Z)) (PreH14 : (0 <= JY_non_alias)) (PreH15 : (JX_non_alias < SM2_P_Z)) (PreH16 : (0 <= JX_non_alias)) (PreH17 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((fp_div2 ((jdouble_trace_t16 (JY_non_alias)))))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_9_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH3 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH5 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH7 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (JX_in_place)))) (PreH9 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH11 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH13 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (mont_p (JY_in_place)))) (PreH15 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH17 : (JZ_in_place < SM2_P_Z)) (PreH18 : (0 <= JZ_in_place)) (PreH19 : (JY_in_place < SM2_P_Z)) (PreH20 : (0 <= JY_in_place)) (PreH21 : (JX_in_place < SM2_P_Z)) (PreH22 : (0 <= JX_in_place)) (PreH23 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH24 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((JX_in_place - (jdouble_trace_z2 (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_9_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH3 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH5 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH7 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH9 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH11 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH13 : (JZ_non_alias < SM2_P_Z)) (PreH14 : (0 <= JZ_non_alias)) (PreH15 : (JY_non_alias < SM2_P_Z)) (PreH16 : (0 <= JY_non_alias)) (PreH17 : (JX_non_alias < SM2_P_Z)) (PreH18 : (0 <= JX_non_alias)) (PreH19 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((JX_non_alias - (jdouble_trace_z2 (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_10_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH5 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH7 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH9 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (JX_in_place)))) (PreH11 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH13 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH15 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (mont_p (JY_in_place)))) (PreH17 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH19 : (JZ_in_place < SM2_P_Z)) (PreH20 : (0 <= JZ_in_place)) (PreH21 : (JY_in_place < SM2_P_Z)) (PreH22 : (0 <= JY_in_place)) (PreH23 : (JX_in_place < SM2_P_Z)) (PreH24 : (0 <= JX_in_place)) (PreH25 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH26 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((JX_in_place + (jdouble_trace_z2 (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_10_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH5 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH7 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH9 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH11 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH13 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH15 : (JZ_non_alias < SM2_P_Z)) (PreH16 : (0 <= JZ_non_alias)) (PreH17 : (JY_non_alias < SM2_P_Z)) (PreH18 : (0 <= JY_non_alias)) (PreH19 : (JX_non_alias < SM2_P_Z)) (PreH20 : (0 <= JX_non_alias)) (PreH21 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((JX_non_alias + (jdouble_trace_z2 (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_11_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH2 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH4 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH8 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH10 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH12 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (JX_in_place)))) (PreH14 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH16 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH18 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (mont_p (JY_in_place)))) (PreH20 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH22 : (JZ_in_place < SM2_P_Z)) (PreH23 : (0 <= JZ_in_place)) (PreH24 : (JY_in_place < SM2_P_Z)) (PreH25 : (0 <= JY_in_place)) (PreH26 : (JX_in_place < SM2_P_Z)) (PreH27 : (0 <= JX_in_place)) (PreH28 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH29 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p (((jdouble_trace_diff (JX_in_place) (JZ_in_place)) * (jdouble_trace_sum (JX_in_place) (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_11_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH2 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH4 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH8 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH10 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH12 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH14 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH16 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH18 : (JZ_non_alias < SM2_P_Z)) (PreH19 : (0 <= JZ_non_alias)) (PreH20 : (JY_non_alias < SM2_P_Z)) (PreH21 : (0 <= JY_non_alias)) (PreH22 : (JX_non_alias < SM2_P_Z)) (PreH23 : (0 <= JX_non_alias)) (PreH24 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p (((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) * (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_12_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH2 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH4 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH10 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH12 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH14 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (JX_in_place)))) (PreH16 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH18 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH20 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (JY_in_place)))) (PreH22 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH24 : (JZ_in_place < SM2_P_Z)) (PreH25 : (0 <= JZ_in_place)) (PreH26 : (JY_in_place < SM2_P_Z)) (PreH27 : (0 <= JY_in_place)) (PreH28 : (JX_in_place < SM2_P_Z)) (PreH29 : (0 <= JX_in_place)) (PreH30 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH31 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((3 * (jdouble_trace_prod (JX_in_place) (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_12_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH2 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH4 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH10 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH12 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH14 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH16 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH18 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH20 : (JZ_non_alias < SM2_P_Z)) (PreH21 : (0 <= JZ_non_alias)) (PreH22 : (JY_non_alias < SM2_P_Z)) (PreH23 : (0 <= JY_non_alias)) (PreH24 : (JX_non_alias < SM2_P_Z)) (PreH25 : (0 <= JX_non_alias)) (PreH26 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((3 * (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_13_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH11 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH13 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH15 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (mont_p (JX_in_place)))) (PreH17 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH19 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH21 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (JY_in_place)))) (PreH23 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH25 : (JZ_in_place < SM2_P_Z)) (PreH26 : (0 <= JZ_in_place)) (PreH27 : (JY_in_place < SM2_P_Z)) (PreH28 : (0 <= JY_in_place)) (PreH29 : (JX_in_place < SM2_P_Z)) (PreH30 : (0 <= JX_in_place)) (PreH31 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH32 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_slope (JX_in_place) (JZ_in_place)) * (jdouble_trace_slope (JX_in_place) (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_13_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH11 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH13 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH15 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH17 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH19 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH21 : (JZ_non_alias < SM2_P_Z)) (PreH22 : (0 <= JZ_non_alias)) (PreH23 : (JY_non_alias < SM2_P_Z)) (PreH24 : (0 <= JY_non_alias)) (PreH25 : (JX_non_alias < SM2_P_Z)) (PreH26 : (0 <= JX_non_alias)) (PreH27 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) * (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_14_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH13 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH15 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH17 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (JX_in_place)))) (PreH19 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH21 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH23 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (mont_p (JY_in_place)))) (PreH25 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH27 : (JZ_in_place < SM2_P_Z)) (PreH28 : (0 <= JZ_in_place)) (PreH29 : (JY_in_place < SM2_P_Z)) (PreH30 : (0 <= JY_in_place)) (PreH31 : (JX_in_place < SM2_P_Z)) (PreH32 : (0 <= JX_in_place)) (PreH33 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH34 : (r_pre = a_pre)) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((2 * (jdouble_trace_s4 (JX_in_place) (JY_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_14_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH13 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH15 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH17 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH19 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH21 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH23 : (JZ_non_alias < SM2_P_Z)) (PreH24 : (0 <= JZ_non_alias)) (PreH25 : (JY_non_alias < SM2_P_Z)) (PreH26 : (0 <= JY_non_alias)) (PreH27 : (JX_non_alias < SM2_P_Z)) (PreH28 : (0 <= JX_non_alias)) (PreH29 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((2 * (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_15_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH4 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH10 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH12 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH14 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH16 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH18 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH20 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (JX_in_place)))) (PreH22 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH24 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH26 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH27 : (0 <= (mont_p (JY_in_place)))) (PreH28 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH30 : (JZ_in_place < SM2_P_Z)) (PreH31 : (0 <= JZ_in_place)) (PreH32 : (JY_in_place < SM2_P_Z)) (PreH33 : (0 <= JY_in_place)) (PreH34 : (JX_in_place < SM2_P_Z)) (PreH35 : (0 <= JX_in_place)) (PreH36 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH37 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) - (jdouble_trace_u8 (JX_in_place) (JY_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_15_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH4 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH10 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH12 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH14 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH16 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH18 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH20 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH22 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH24 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH26 : (JZ_non_alias < SM2_P_Z)) (PreH27 : (0 <= JZ_non_alias)) (PreH28 : (JY_non_alias < SM2_P_Z)) (PreH29 : (0 <= JY_non_alias)) (PreH30 : (JX_non_alias < SM2_P_Z)) (PreH31 : (0 <= JX_non_alias)) (PreH32 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) - (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_16_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH5 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH15 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH17 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH19 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH21 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (mont_p (JX_in_place)))) (PreH23 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH25 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH27 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (mont_p (JY_in_place)))) (PreH29 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH31 : (JZ_in_place < SM2_P_Z)) (PreH32 : (0 <= JZ_in_place)) (PreH33 : (JY_in_place < SM2_P_Z)) (PreH34 : (0 <= JY_in_place)) (PreH35 : (JX_in_place < SM2_P_Z)) (PreH36 : (0 <= JX_in_place)) (PreH37 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH38 : (r_pre = a_pre)) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_s4 (JX_in_place) (JY_in_place)) - (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_16_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH5 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH15 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH17 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH19 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH21 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH23 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH25 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH27 : (JZ_non_alias < SM2_P_Z)) (PreH28 : (0 <= JZ_non_alias)) (PreH29 : (JY_non_alias < SM2_P_Z)) (PreH30 : (0 <= JY_non_alias)) (PreH31 : (JX_non_alias < SM2_P_Z)) (PreH32 : (0 <= JX_non_alias)) (PreH33 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) - (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_17_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH4 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH8 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH10 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH12 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH14 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH16 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH18 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH20 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH22 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH24 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (mont_p (JX_in_place)))) (PreH26 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH28 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH30 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH31 : (0 <= (mont_p (JY_in_place)))) (PreH32 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH33 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH34 : (JZ_in_place < SM2_P_Z)) (PreH35 : (0 <= JZ_in_place)) (PreH36 : (JY_in_place < SM2_P_Z)) (PreH37 : (0 <= JY_in_place)) (PreH38 : (JX_in_place < SM2_P_Z)) (PreH39 : (0 <= JX_in_place)) (PreH40 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH41 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_slope (JX_in_place) (JZ_in_place)) * (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_17_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH2 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH4 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH8 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH10 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH12 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH14 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH16 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH18 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH20 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH22 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH24 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH26 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH28 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH30 : (JZ_non_alias < SM2_P_Z)) (PreH31 : (0 <= JZ_non_alias)) (PreH32 : (JY_non_alias < SM2_P_Z)) (PreH33 : (0 <= JY_non_alias)) (PreH34 : (JX_non_alias < SM2_P_Z)) (PreH35 : (0 <= JX_non_alias)) (PreH36 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p (((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) * (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  (“ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ))
.

Definition montg_double_jpoint_entail_wit_18_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH9 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH15 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH17 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH19 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH21 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH23 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH25 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (mont_p (JX_in_place)))) (PreH27 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH29 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH31 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH32 : (0 <= (mont_p (JY_in_place)))) (PreH33 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH34 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH35 : (JZ_in_place < SM2_P_Z)) (PreH36 : (0 <= JZ_in_place)) (PreH37 : (JY_in_place < SM2_P_Z)) (PreH38 : (0 <= JY_in_place)) (PreH39 : (JX_in_place < SM2_P_Z)) (PreH40 : (0 <= JX_in_place)) (PreH41 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH42 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) - (jdouble_trace_t8 (JY_in_place)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_double_jpoint_entail_wit_18_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH9 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH15 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH17 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH19 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH21 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH23 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH25 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH27 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH29 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH31 : (JZ_non_alias < SM2_P_Z)) (PreH32 : (0 <= JZ_non_alias)) (PreH33 : (JY_non_alias < SM2_P_Z)) (PreH34 : (0 <= JY_non_alias)) (PreH35 : (JX_non_alias < SM2_P_Z)) (PreH36 : (0 <= JX_non_alias)) (PreH37 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) - (jdouble_trace_t8 (JY_non_alias)) ))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_double_jpoint_return_wit_1_in_place := 
(
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH11 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH15 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH17 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH19 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH21 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH23 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH25 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH27 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (mont_p (JX_in_place)))) (PreH29 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH31 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH32 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH33 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH34 : (0 <= (mont_p (JY_in_place)))) (PreH35 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH36 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH37 : (JZ_in_place < SM2_P_Z)) (PreH38 : (0 <= JZ_in_place)) (PreH39 : (JY_in_place < SM2_P_Z)) (PreH40 : (0 <= JY_in_place)) (PreH41 : (JX_in_place < SM2_P_Z)) (PreH42 : (0 <= JX_in_place)) (PreH43 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH44 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
|--
  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_double (P_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH11 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH15 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH17 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH19 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH21 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH23 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH25 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH27 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (mont_p (JX_in_place)))) (PreH29 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH31 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH32 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH33 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH34 : (0 <= (mont_p (JY_in_place)))) (PreH35 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH36 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH37 : (JZ_in_place < SM2_P_Z)) (PreH38 : (0 <= JZ_in_place)) (PreH39 : (JY_in_place < SM2_P_Z)) (PreH40 : (0 <= JY_in_place)) (PreH41 : (JX_in_place < SM2_P_Z)) (PreH42 : (0 <= JX_in_place)) (PreH43 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH44 : (r_pre = a_pre)) ,
  TT && emp 
|--
  EX (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) = (mont_p (z))) ” 
  &&  “ ((mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) = (mont_p (x))) ” 
  &&  “ ((mont_p ((jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)))) = (mont_p (y))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x y z (sm2_point_double (P_in_place)) ) ”
  &&  emp
).

Definition montg_double_jpoint_return_wit_2_non_alias := 
(
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH11 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH15 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH17 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH19 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH21 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH23 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH25 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH27 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH29 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH31 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH32 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH33 : (JZ_non_alias < SM2_P_Z)) (PreH34 : (0 <= JZ_non_alias)) (PreH35 : (JY_non_alias < SM2_P_Z)) (PreH36 : (0 <= JY_non_alias)) (PreH37 : (JX_non_alias < SM2_P_Z)) (PreH38 : (0 <= JX_non_alias)) (PreH39 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH11 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH15 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH17 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH19 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH21 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH23 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH25 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH27 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH29 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH30 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH31 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH32 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH33 : (JZ_non_alias < SM2_P_Z)) (PreH34 : (0 <= JZ_non_alias)) (PreH35 : (JY_non_alias < SM2_P_Z)) (PreH36 : (0 <= JY_non_alias)) (PreH37 : (JX_non_alias < SM2_P_Z)) (PreH38 : (0 <= JX_non_alias)) (PreH39 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  TT && emp 
|--
  EX (z_2: Z)  (y_2: Z)  (x_2: Z)  (z: Z)  (y: Z)  (x: Z) ,
  “ ((mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) = (mont_p (z_2))) ” 
  &&  “ ((mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) = (mont_p (x_2))) ” 
  &&  “ ((mont_p ((jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) = (mont_p (y_2))) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 (sm2_point_double (P_non_alias)) ) ” 
  &&  “ ((mont_p (JY_non_alias)) = (mont_p (y))) ” 
  &&  “ ((mont_p (JZ_non_alias)) = (mont_p (z))) ” 
  &&  “ ((mont_p (JX_non_alias)) = (mont_p (x))) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_represents x y z P_non_alias ) ”
  &&  emp
).

Definition montg_double_jpoint_partial_solve_wit_1_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_double_jpoint_partial_solve_wit_2_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (PreH1 : (r_pre = a_pre)) ,
  (store_mont_jpoint a_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint a_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_double_jpoint_partial_solve_wit_3_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y"))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (JZ_in_place < SM2_P_Z)) (PreH5 : (0 <= JZ_in_place)) (PreH6 : (JY_in_place < SM2_P_Z)) (PreH7 : (0 <= JY_in_place)) (PreH8 : (JX_in_place < SM2_P_Z)) (PreH9 : (0 <= JX_in_place)) (PreH10 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH11 : (r_pre = a_pre)) ,
  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (store_jpoint_fields a_pre (mont_p (JX_in_place)) (mont_p (JY_in_place)) (mont_p (JZ_in_place)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= JZ_in_place) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_3_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (&((r_pre)  # "JPoint" ->ₛ "y") = &((r_pre)  # "JPoint" ->ₛ "y"))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (JZ_in_place < SM2_P_Z)) (PreH5 : (0 <= JZ_in_place)) (PreH6 : (JY_in_place < SM2_P_Z)) (PreH7 : (0 <= JY_in_place)) (PreH8 : (JX_in_place < SM2_P_Z)) (PreH9 : (0 <= JX_in_place)) (PreH10 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH11 : (r_pre = a_pre)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (store_jpoint_fields a_pre (mont_p (JX_in_place)) (mont_p (JY_in_place)) (mont_p (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= JZ_in_place) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (UInt64Array.undef_full &(( &( "Zsqr" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_3_in_place := montg_double_jpoint_partial_solve_wit_3_in_place_pure -> montg_double_jpoint_partial_solve_wit_3_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_4_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (JZ_non_alias < SM2_P_Z)) (PreH2 : (0 <= JZ_non_alias)) (PreH3 : (JY_non_alias < SM2_P_Z)) (PreH4 : (0 <= JY_non_alias)) (PreH5 : (JX_non_alias < SM2_P_Z)) (PreH6 : (0 <= JX_non_alias)) (PreH7 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  (store_jpoint_fields a_pre (mont_p (JX_non_alias)) (mont_p (JY_non_alias)) (mont_p (JZ_non_alias)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= JZ_non_alias) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_4_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (JZ_non_alias < SM2_P_Z)) (PreH2 : (0 <= JZ_non_alias)) (PreH3 : (JY_non_alias < SM2_P_Z)) (PreH4 : (0 <= JY_non_alias)) (PreH5 : (JX_non_alias < SM2_P_Z)) (PreH6 : (0 <= JX_non_alias)) (PreH7 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zsqr" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (store_jpoint_fields a_pre (mont_p (JX_non_alias)) (mont_p (JY_non_alias)) (mont_p (JZ_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= JZ_non_alias) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "Zsqr" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_4_non_alias := montg_double_jpoint_partial_solve_wit_4_non_alias_pure -> montg_double_jpoint_partial_solve_wit_4_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_5_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH3 : (JZ_in_place < SM2_P_Z)) (PreH4 : (0 <= JZ_in_place)) (PreH5 : (JY_in_place < SM2_P_Z)) (PreH6 : (0 <= JY_in_place)) (PreH7 : (JX_in_place < SM2_P_Z)) (PreH8 : (0 <= JX_in_place)) (PreH9 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH10 : (r_pre = a_pre)) ,
  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= JY_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_5_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH3 : (JZ_in_place < SM2_P_Z)) (PreH4 : (0 <= JZ_in_place)) (PreH5 : (JY_in_place < SM2_P_Z)) (PreH6 : (0 <= JY_in_place)) (PreH7 : (JX_in_place < SM2_P_Z)) (PreH8 : (0 <= JX_in_place)) (PreH9 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH10 : (r_pre = a_pre)) ,
  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (0 <= JY_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_5_in_place := montg_double_jpoint_partial_solve_wit_5_in_place_pure -> montg_double_jpoint_partial_solve_wit_5_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_6_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH3 : (JZ_non_alias < SM2_P_Z)) (PreH4 : (0 <= JZ_non_alias)) (PreH5 : (JY_non_alias < SM2_P_Z)) (PreH6 : (0 <= JY_non_alias)) (PreH7 : (JX_non_alias < SM2_P_Z)) (PreH8 : (0 <= JX_non_alias)) (PreH9 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= JY_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_6_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH3 : (JZ_non_alias < SM2_P_Z)) (PreH4 : (0 <= JZ_non_alias)) (PreH5 : (JY_non_alias < SM2_P_Z)) (PreH6 : (0 <= JY_non_alias)) (PreH7 : (JX_non_alias < SM2_P_Z)) (PreH8 : (0 <= JX_non_alias)) (PreH9 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= JY_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_6_non_alias := montg_double_jpoint_partial_solve_wit_6_non_alias_pure -> montg_double_jpoint_partial_solve_wit_6_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_7_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH3 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (JY_in_place)))) (PreH5 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH7 : (JZ_in_place < SM2_P_Z)) (PreH8 : (0 <= JZ_in_place)) (PreH9 : (JY_in_place < SM2_P_Z)) (PreH10 : (0 <= JY_in_place)) (PreH11 : (JX_in_place < SM2_P_Z)) (PreH12 : (0 <= JX_in_place)) (PreH13 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH14 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_7_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH3 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (JY_in_place)))) (PreH5 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH7 : (JZ_in_place < SM2_P_Z)) (PreH8 : (0 <= JZ_in_place)) (PreH9 : (JY_in_place < SM2_P_Z)) (PreH10 : (0 <= JY_in_place)) (PreH11 : (JX_in_place < SM2_P_Z)) (PreH12 : (0 <= JX_in_place)) (PreH13 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH14 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_7_in_place := montg_double_jpoint_partial_solve_wit_7_in_place_pure -> montg_double_jpoint_partial_solve_wit_7_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_8_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH3 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH5 : (JZ_non_alias < SM2_P_Z)) (PreH6 : (0 <= JZ_non_alias)) (PreH7 : (JY_non_alias < SM2_P_Z)) (PreH8 : (0 <= JY_non_alias)) (PreH9 : (JX_non_alias < SM2_P_Z)) (PreH10 : (0 <= JX_non_alias)) (PreH11 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_8_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH3 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH5 : (JZ_non_alias < SM2_P_Z)) (PreH6 : (0 <= JZ_non_alias)) (PreH7 : (JY_non_alias < SM2_P_Z)) (PreH8 : (0 <= JY_non_alias)) (PreH9 : (JX_non_alias < SM2_P_Z)) (PreH10 : (0 <= JX_non_alias)) (PreH11 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_8_non_alias := montg_double_jpoint_partial_solve_wit_8_non_alias_pure -> montg_double_jpoint_partial_solve_wit_8_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_9_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH4 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (JY_in_place)))) (PreH6 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH8 : (JZ_in_place < SM2_P_Z)) (PreH9 : (0 <= JZ_in_place)) (PreH10 : (JY_in_place < SM2_P_Z)) (PreH11 : (0 <= JY_in_place)) (PreH12 : (JX_in_place < SM2_P_Z)) (PreH13 : (0 <= JX_in_place)) (PreH14 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH15 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_9_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((r_pre)  # "JPoint" ->ₛ "z") = &((r_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH3 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH4 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (mont_p (JY_in_place)))) (PreH6 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH8 : (JZ_in_place < SM2_P_Z)) (PreH9 : (0 <= JZ_in_place)) (PreH10 : (JY_in_place < SM2_P_Z)) (PreH11 : (0 <= JY_in_place)) (PreH12 : (JX_in_place < SM2_P_Z)) (PreH13 : (0 <= JX_in_place)) (PreH14 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH15 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_9_in_place := montg_double_jpoint_partial_solve_wit_9_in_place_pure -> montg_double_jpoint_partial_solve_wit_9_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_10_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH3 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH5 : (JZ_non_alias < SM2_P_Z)) (PreH6 : (0 <= JZ_non_alias)) (PreH7 : (JY_non_alias < SM2_P_Z)) (PreH8 : (0 <= JY_non_alias)) (PreH9 : (JX_non_alias < SM2_P_Z)) (PreH10 : (0 <= JX_non_alias)) (PreH11 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_10_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH3 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH5 : (JZ_non_alias < SM2_P_Z)) (PreH6 : (0 <= JZ_non_alias)) (PreH7 : (JY_non_alias < SM2_P_Z)) (PreH8 : (0 <= JY_non_alias)) (PreH9 : (JX_non_alias < SM2_P_Z)) (PreH10 : (0 <= JX_non_alias)) (PreH11 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_s2 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_10_non_alias := montg_double_jpoint_partial_solve_wit_10_non_alias_pure -> montg_double_jpoint_partial_solve_wit_10_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_11_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH6 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (JY_in_place)))) (PreH8 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH10 : (JZ_in_place < SM2_P_Z)) (PreH11 : (0 <= JZ_in_place)) (PreH12 : (JY_in_place < SM2_P_Z)) (PreH13 : (0 <= JY_in_place)) (PreH14 : (JX_in_place < SM2_P_Z)) (PreH15 : (0 <= JX_in_place)) (PreH16 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH17 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_11_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH6 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (JY_in_place)))) (PreH8 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH10 : (JZ_in_place < SM2_P_Z)) (PreH11 : (0 <= JZ_in_place)) (PreH12 : (JY_in_place < SM2_P_Z)) (PreH13 : (0 <= JY_in_place)) (PreH14 : (JX_in_place < SM2_P_Z)) (PreH15 : (0 <= JX_in_place)) (PreH16 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH17 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (UInt64Array.undef_full &(( &( "U2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_11_in_place := montg_double_jpoint_partial_solve_wit_11_in_place_pure -> montg_double_jpoint_partial_solve_wit_11_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_12_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH6 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH8 : (JZ_non_alias < SM2_P_Z)) (PreH9 : (0 <= JZ_non_alias)) (PreH10 : (JY_non_alias < SM2_P_Z)) (PreH11 : (0 <= JY_non_alias)) (PreH12 : (JX_non_alias < SM2_P_Z)) (PreH13 : (0 <= JX_non_alias)) (PreH14 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_12_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH6 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH8 : (JZ_non_alias < SM2_P_Z)) (PreH9 : (0 <= JZ_non_alias)) (PreH10 : (JY_non_alias < SM2_P_Z)) (PreH11 : (0 <= JY_non_alias)) (PreH12 : (JX_non_alias < SM2_P_Z)) (PreH13 : (0 <= JX_non_alias)) (PreH14 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U2" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "U2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_12_non_alias := montg_double_jpoint_partial_solve_wit_12_non_alias_pure -> montg_double_jpoint_partial_solve_wit_12_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_13_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH3 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (JX_in_place)))) (PreH5 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH7 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH9 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (JY_in_place)))) (PreH11 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH13 : (JZ_in_place < SM2_P_Z)) (PreH14 : (0 <= JZ_in_place)) (PreH15 : (JY_in_place < SM2_P_Z)) (PreH16 : (0 <= JY_in_place)) (PreH17 : (JX_in_place < SM2_P_Z)) (PreH18 : (0 <= JX_in_place)) (PreH19 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH20 : (r_pre = a_pre)) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_13_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH3 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (JX_in_place)))) (PreH5 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH7 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH9 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (JY_in_place)))) (PreH11 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH13 : (JZ_in_place < SM2_P_Z)) (PreH14 : (0 <= JZ_in_place)) (PreH15 : (JY_in_place < SM2_P_Z)) (PreH16 : (0 <= JY_in_place)) (PreH17 : (JX_in_place < SM2_P_Z)) (PreH18 : (0 <= JX_in_place)) (PreH19 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH20 : (r_pre = a_pre)) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_13_in_place := montg_double_jpoint_partial_solve_wit_13_in_place_pure -> montg_double_jpoint_partial_solve_wit_13_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_14_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH3 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH5 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH7 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_14_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH3 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH5 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH7 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH9 : (JZ_non_alias < SM2_P_Z)) (PreH10 : (0 <= JZ_non_alias)) (PreH11 : (JY_non_alias < SM2_P_Z)) (PreH12 : (0 <= JY_non_alias)) (PreH13 : (JX_non_alias < SM2_P_Z)) (PreH14 : (0 <= JX_non_alias)) (PreH15 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_m4 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_14_non_alias := montg_double_jpoint_partial_solve_wit_14_non_alias_pure -> montg_double_jpoint_partial_solve_wit_14_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_15_in_place_pure := 
(
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH6 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (JX_in_place)))) (PreH8 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH10 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH12 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (JY_in_place)))) (PreH14 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH16 : (JZ_in_place < SM2_P_Z)) (PreH17 : (0 <= JZ_in_place)) (PreH18 : (JY_in_place < SM2_P_Z)) (PreH19 : (0 <= JY_in_place)) (PreH20 : (JX_in_place < SM2_P_Z)) (PreH21 : (0 <= JX_in_place)) (PreH22 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH23 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (( &( "U3" ) ) <> ( &( "T" ) )) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH3 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH5 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (JX_in_place)))) (PreH7 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH9 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH11 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (mont_p (JY_in_place)))) (PreH13 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH15 : (JZ_in_place < SM2_P_Z)) (PreH16 : (0 <= JZ_in_place)) (PreH17 : (JY_in_place < SM2_P_Z)) (PreH18 : (0 <= JY_in_place)) (PreH19 : (JX_in_place < SM2_P_Z)) (PreH20 : (0 <= JX_in_place)) (PreH21 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH22 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "U3" ) ) <> ( &( "T" ) )) ”
).

Definition montg_double_jpoint_partial_solve_wit_15_in_place_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH3 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH5 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (mont_p (JX_in_place)))) (PreH7 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH9 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH11 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (mont_p (JY_in_place)))) (PreH13 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH15 : (JZ_in_place < SM2_P_Z)) (PreH16 : (0 <= JZ_in_place)) (PreH17 : (JY_in_place < SM2_P_Z)) (PreH18 : (0 <= JY_in_place)) (PreH19 : (JX_in_place < SM2_P_Z)) (PreH20 : (0 <= JX_in_place)) (PreH21 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH22 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "U3" ) ) <> ( &( "T" ) )) ”
.

Definition montg_double_jpoint_partial_solve_wit_15_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH6 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (mont_p (JX_in_place)))) (PreH8 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH10 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH12 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (JY_in_place)))) (PreH14 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH16 : (JZ_in_place < SM2_P_Z)) (PreH17 : (0 <= JZ_in_place)) (PreH18 : (JY_in_place < SM2_P_Z)) (PreH19 : (0 <= JY_in_place)) (PreH20 : (JX_in_place < SM2_P_Z)) (PreH21 : (0 <= JX_in_place)) (PreH22 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH23 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (( &( "U3" ) ) <> ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (UInt64Array.undef_full &(( &( "U3" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_15_in_place := montg_double_jpoint_partial_solve_wit_15_in_place_pure -> montg_double_jpoint_partial_solve_wit_15_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_16_non_alias_pure := 
(
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH6 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH8 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH10 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (( &( "U3" ) ) <> ( &( "T" ) )) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH3 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH5 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH7 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH9 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH11 : (JZ_non_alias < SM2_P_Z)) (PreH12 : (0 <= JZ_non_alias)) (PreH13 : (JY_non_alias < SM2_P_Z)) (PreH14 : (0 <= JY_non_alias)) (PreH15 : (JX_non_alias < SM2_P_Z)) (PreH16 : (0 <= JX_non_alias)) (PreH17 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "U3" ) ) <> ( &( "T" ) )) ”
).

Definition montg_double_jpoint_partial_solve_wit_16_non_alias_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH3 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH5 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH7 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH9 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH11 : (JZ_non_alias < SM2_P_Z)) (PreH12 : (0 <= JZ_non_alias)) (PreH13 : (JY_non_alias < SM2_P_Z)) (PreH14 : (0 <= JY_non_alias)) (PreH15 : (JX_non_alias < SM2_P_Z)) (PreH16 : (0 <= JX_non_alias)) (PreH17 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "U3" ) ) <> ( &( "T" ) )) ”
.

Definition montg_double_jpoint_partial_solve_wit_16_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH6 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH8 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH10 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH12 : (JZ_non_alias < SM2_P_Z)) (PreH13 : (0 <= JZ_non_alias)) (PreH14 : (JY_non_alias < SM2_P_Z)) (PreH15 : (0 <= JY_non_alias)) (PreH16 : (JX_non_alias < SM2_P_Z)) (PreH17 : (0 <= JX_non_alias)) (PreH18 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U3" ) ) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (( &( "U3" ) ) <> ( &( "T" ) )) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (UInt64Array.undef_full &(( &( "U3" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_16_non_alias := montg_double_jpoint_partial_solve_wit_16_non_alias_pure -> montg_double_jpoint_partial_solve_wit_16_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_17_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH3 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH5 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH7 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (JX_in_place)))) (PreH9 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH11 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH13 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (mont_p (JY_in_place)))) (PreH15 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH17 : (JZ_in_place < SM2_P_Z)) (PreH18 : (0 <= JZ_in_place)) (PreH19 : (JY_in_place < SM2_P_Z)) (PreH20 : (0 <= JY_in_place)) (PreH21 : (JX_in_place < SM2_P_Z)) (PreH22 : (0 <= JX_in_place)) (PreH23 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH24 : (r_pre = a_pre)) ,
  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= JX_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_17_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH3 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH5 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH7 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (mont_p (JX_in_place)))) (PreH9 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH11 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH13 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (mont_p (JY_in_place)))) (PreH15 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH17 : (JZ_in_place < SM2_P_Z)) (PreH18 : (0 <= JZ_in_place)) (PreH19 : (JY_in_place < SM2_P_Z)) (PreH20 : (0 <= JY_in_place)) (PreH21 : (JX_in_place < SM2_P_Z)) (PreH22 : (0 <= JX_in_place)) (PreH23 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH24 : (r_pre = a_pre)) ,
  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (0 <= JX_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
.

Definition montg_double_jpoint_partial_solve_wit_17_in_place := montg_double_jpoint_partial_solve_wit_17_in_place_pure -> montg_double_jpoint_partial_solve_wit_17_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_18_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH3 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH5 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH7 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH9 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH11 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH13 : (JZ_non_alias < SM2_P_Z)) (PreH14 : (0 <= JZ_non_alias)) (PreH15 : (JY_non_alias < SM2_P_Z)) (PreH16 : (0 <= JY_non_alias)) (PreH17 : (JX_non_alias < SM2_P_Z)) (PreH18 : (0 <= JX_non_alias)) (PreH19 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= JX_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_18_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH3 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH5 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH7 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH9 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH11 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH13 : (JZ_non_alias < SM2_P_Z)) (PreH14 : (0 <= JZ_non_alias)) (PreH15 : (JY_non_alias < SM2_P_Z)) (PreH16 : (0 <= JY_non_alias)) (PreH17 : (JX_non_alias < SM2_P_Z)) (PreH18 : (0 <= JX_non_alias)) (PreH19 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= JX_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_18_non_alias := montg_double_jpoint_partial_solve_wit_18_non_alias_pure -> montg_double_jpoint_partial_solve_wit_18_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_19_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH5 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH7 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH9 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (JX_in_place)))) (PreH11 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH13 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH15 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (mont_p (JY_in_place)))) (PreH17 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH19 : (JZ_in_place < SM2_P_Z)) (PreH20 : (0 <= JZ_in_place)) (PreH21 : (JY_in_place < SM2_P_Z)) (PreH22 : (0 <= JY_in_place)) (PreH23 : (JX_in_place < SM2_P_Z)) (PreH24 : (0 <= JX_in_place)) (PreH25 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH26 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= JX_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_19_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH5 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH7 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH9 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (mont_p (JX_in_place)))) (PreH11 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH13 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH15 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (mont_p (JY_in_place)))) (PreH17 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH19 : (JZ_in_place < SM2_P_Z)) (PreH20 : (0 <= JZ_in_place)) (PreH21 : (JY_in_place < SM2_P_Z)) (PreH22 : (0 <= JY_in_place)) (PreH23 : (JX_in_place < SM2_P_Z)) (PreH24 : (0 <= JX_in_place)) (PreH25 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH26 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
|--
  “ (0 <= JX_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (UInt64Array.undef_full &(( &( "U1" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_19_in_place := montg_double_jpoint_partial_solve_wit_19_in_place_pure -> montg_double_jpoint_partial_solve_wit_19_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_20_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH5 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH7 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH9 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH11 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH13 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH15 : (JZ_non_alias < SM2_P_Z)) (PreH16 : (0 <= JZ_non_alias)) (PreH17 : (JY_non_alias < SM2_P_Z)) (PreH18 : (0 <= JY_non_alias)) (PreH19 : (JX_non_alias < SM2_P_Z)) (PreH20 : (0 <= JX_non_alias)) (PreH21 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= JX_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_20_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH5 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH7 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH9 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH11 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH13 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH15 : (JZ_non_alias < SM2_P_Z)) (PreH16 : (0 <= JZ_non_alias)) (PreH17 : (JY_non_alias < SM2_P_Z)) (PreH18 : (0 <= JY_non_alias)) (PreH19 : (JX_non_alias < SM2_P_Z)) (PreH20 : (0 <= JX_non_alias)) (PreH21 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UndefStructPredu32 ( &( "U1" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= JX_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (UInt64Array.undef_full &(( &( "U1" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_20_non_alias := montg_double_jpoint_partial_solve_wit_20_non_alias_pure -> montg_double_jpoint_partial_solve_wit_20_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_21_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH7 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH9 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH11 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (mont_p (JX_in_place)))) (PreH13 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH15 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH17 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (JY_in_place)))) (PreH19 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH21 : (JZ_in_place < SM2_P_Z)) (PreH22 : (0 <= JZ_in_place)) (PreH23 : (JY_in_place < SM2_P_Z)) (PreH24 : (0 <= JY_in_place)) (PreH25 : (JX_in_place < SM2_P_Z)) (PreH26 : (0 <= JX_in_place)) (PreH27 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH28 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_21_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH7 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH9 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH11 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (mont_p (JX_in_place)))) (PreH13 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH15 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH17 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (JY_in_place)))) (PreH19 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH21 : (JZ_in_place < SM2_P_Z)) (PreH22 : (0 <= JZ_in_place)) (PreH23 : (JY_in_place < SM2_P_Z)) (PreH24 : (0 <= JY_in_place)) (PreH25 : (JX_in_place < SM2_P_Z)) (PreH26 : (0 <= JX_in_place)) (PreH27 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH28 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_21_in_place := montg_double_jpoint_partial_solve_wit_21_in_place_pure -> montg_double_jpoint_partial_solve_wit_21_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_22_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH7 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH9 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH11 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH13 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH15 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH17 : (JZ_non_alias < SM2_P_Z)) (PreH18 : (0 <= JZ_non_alias)) (PreH19 : (JY_non_alias < SM2_P_Z)) (PreH20 : (0 <= JY_non_alias)) (PreH21 : (JX_non_alias < SM2_P_Z)) (PreH22 : (0 <= JX_non_alias)) (PreH23 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_22_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH7 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH9 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH11 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH13 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH15 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH17 : (JZ_non_alias < SM2_P_Z)) (PreH18 : (0 <= JZ_non_alias)) (PreH19 : (JY_non_alias < SM2_P_Z)) (PreH20 : (0 <= JY_non_alias)) (PreH21 : (JX_non_alias < SM2_P_Z)) (PreH22 : (0 <= JX_non_alias)) (PreH23 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_22_non_alias := montg_double_jpoint_partial_solve_wit_22_non_alias_pure -> montg_double_jpoint_partial_solve_wit_22_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_23_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH10 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH12 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH14 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (JX_in_place)))) (PreH16 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH18 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH20 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (JY_in_place)))) (PreH22 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH24 : (JZ_in_place < SM2_P_Z)) (PreH25 : (0 <= JZ_in_place)) (PreH26 : (JY_in_place < SM2_P_Z)) (PreH27 : (0 <= JY_in_place)) (PreH28 : (JX_in_place < SM2_P_Z)) (PreH29 : (0 <= JX_in_place)) (PreH30 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH31 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_23_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH10 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH12 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH14 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (mont_p (JX_in_place)))) (PreH16 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH18 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH20 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (mont_p (JY_in_place)))) (PreH22 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH24 : (JZ_in_place < SM2_P_Z)) (PreH25 : (0 <= JZ_in_place)) (PreH26 : (JY_in_place < SM2_P_Z)) (PreH27 : (0 <= JY_in_place)) (PreH28 : (JX_in_place < SM2_P_Z)) (PreH29 : (0 <= JX_in_place)) (PreH30 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH31 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_23_in_place := montg_double_jpoint_partial_solve_wit_23_in_place_pure -> montg_double_jpoint_partial_solve_wit_23_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_24_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH10 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH12 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH14 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH16 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH18 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH20 : (JZ_non_alias < SM2_P_Z)) (PreH21 : (0 <= JZ_non_alias)) (PreH22 : (JY_non_alias < SM2_P_Z)) (PreH23 : (0 <= JY_non_alias)) (PreH24 : (JX_non_alias < SM2_P_Z)) (PreH25 : (0 <= JX_non_alias)) (PreH26 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_24_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH10 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH12 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH14 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH16 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH18 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH20 : (JZ_non_alias < SM2_P_Z)) (PreH21 : (0 <= JZ_non_alias)) (PreH22 : (JY_non_alias < SM2_P_Z)) (PreH23 : (0 <= JY_non_alias)) (PreH24 : (JX_non_alias < SM2_P_Z)) (PreH25 : (0 <= JX_non_alias)) (PreH26 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "U1" ) ) = ( &( "U1" ) )) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_24_non_alias := montg_double_jpoint_partial_solve_wit_24_non_alias_pure -> montg_double_jpoint_partial_solve_wit_24_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_25_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH10 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH12 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH14 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH16 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (JX_in_place)))) (PreH18 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH20 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH22 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (JY_in_place)))) (PreH24 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH26 : (JZ_in_place < SM2_P_Z)) (PreH27 : (0 <= JZ_in_place)) (PreH28 : (JY_in_place < SM2_P_Z)) (PreH29 : (0 <= JY_in_place)) (PreH30 : (JX_in_place < SM2_P_Z)) (PreH31 : (0 <= JX_in_place)) (PreH32 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH33 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_25_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH10 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH12 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH14 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH16 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (mont_p (JX_in_place)))) (PreH18 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH20 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH22 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (JY_in_place)))) (PreH24 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH26 : (JZ_in_place < SM2_P_Z)) (PreH27 : (0 <= JZ_in_place)) (PreH28 : (JY_in_place < SM2_P_Z)) (PreH29 : (0 <= JY_in_place)) (PreH30 : (JX_in_place < SM2_P_Z)) (PreH31 : (0 <= JX_in_place)) (PreH32 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH33 : (r_pre = a_pre)) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_25_in_place := montg_double_jpoint_partial_solve_wit_25_in_place_pure -> montg_double_jpoint_partial_solve_wit_25_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_26_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH10 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH12 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH14 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH16 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH18 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH20 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH22 : (JZ_non_alias < SM2_P_Z)) (PreH23 : (0 <= JZ_non_alias)) (PreH24 : (JY_non_alias < SM2_P_Z)) (PreH25 : (0 <= JY_non_alias)) (PreH26 : (JX_non_alias < SM2_P_Z)) (PreH27 : (0 <= JX_non_alias)) (PreH28 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_26_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH3 : (( &( "U1" ) ) = ( &( "U1" ) ))) (PreH4 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH10 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH12 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH14 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH16 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH18 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH20 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH22 : (JZ_non_alias < SM2_P_Z)) (PreH23 : (0 <= JZ_non_alias)) (PreH24 : (JY_non_alias < SM2_P_Z)) (PreH25 : (0 <= JY_non_alias)) (PreH26 : (JX_non_alias < SM2_P_Z)) (PreH27 : (0 <= JX_non_alias)) (PreH28 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_26_non_alias := montg_double_jpoint_partial_solve_wit_26_non_alias_pure -> montg_double_jpoint_partial_solve_wit_26_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_27_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH13 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH15 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH17 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (JX_in_place)))) (PreH19 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH21 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH23 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (mont_p (JY_in_place)))) (PreH25 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH27 : (JZ_in_place < SM2_P_Z)) (PreH28 : (0 <= JZ_in_place)) (PreH29 : (JY_in_place < SM2_P_Z)) (PreH30 : (0 <= JY_in_place)) (PreH31 : (JX_in_place < SM2_P_Z)) (PreH32 : (0 <= JX_in_place)) (PreH33 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH34 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_27_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH13 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH15 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH17 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (mont_p (JX_in_place)))) (PreH19 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH21 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH23 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (mont_p (JY_in_place)))) (PreH25 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH27 : (JZ_in_place < SM2_P_Z)) (PreH28 : (0 <= JZ_in_place)) (PreH29 : (JY_in_place < SM2_P_Z)) (PreH30 : (0 <= JY_in_place)) (PreH31 : (JX_in_place < SM2_P_Z)) (PreH32 : (0 <= JX_in_place)) (PreH33 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH34 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_in_place)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_27_in_place := montg_double_jpoint_partial_solve_wit_27_in_place_pure -> montg_double_jpoint_partial_solve_wit_27_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_28_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH13 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH15 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH17 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH19 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH21 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH23 : (JZ_non_alias < SM2_P_Z)) (PreH24 : (0 <= JZ_non_alias)) (PreH25 : (JY_non_alias < SM2_P_Z)) (PreH26 : (0 <= JY_non_alias)) (PreH27 : (JX_non_alias < SM2_P_Z)) (PreH28 : (0 <= JX_non_alias)) (PreH29 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_28_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH13 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH15 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH17 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH19 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH21 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH23 : (JZ_non_alias < SM2_P_Z)) (PreH24 : (0 <= JZ_non_alias)) (PreH25 : (JY_non_alias < SM2_P_Z)) (PreH26 : (0 <= JY_non_alias)) (PreH27 : (JX_non_alias < SM2_P_Z)) (PreH28 : (0 <= JX_non_alias)) (PreH29 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_28_non_alias := montg_double_jpoint_partial_solve_wit_28_non_alias_pure -> montg_double_jpoint_partial_solve_wit_28_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_29_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH3 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH15 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH17 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH19 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (JX_in_place)))) (PreH21 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH23 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH25 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (mont_p (JY_in_place)))) (PreH27 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH29 : (JZ_in_place < SM2_P_Z)) (PreH30 : (0 <= JZ_in_place)) (PreH31 : (JY_in_place < SM2_P_Z)) (PreH32 : (0 <= JY_in_place)) (PreH33 : (JX_in_place < SM2_P_Z)) (PreH34 : (0 <= JX_in_place)) (PreH35 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH36 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_29_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH3 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH7 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH15 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH17 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH19 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (mont_p (JX_in_place)))) (PreH21 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH23 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH25 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (mont_p (JY_in_place)))) (PreH27 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH29 : (JZ_in_place < SM2_P_Z)) (PreH30 : (0 <= JZ_in_place)) (PreH31 : (JY_in_place < SM2_P_Z)) (PreH32 : (0 <= JY_in_place)) (PreH33 : (JX_in_place < SM2_P_Z)) (PreH34 : (0 <= JX_in_place)) (PreH35 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH36 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_in_place) (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_29_in_place := montg_double_jpoint_partial_solve_wit_29_in_place_pure -> montg_double_jpoint_partial_solve_wit_29_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_30_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH3 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH15 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH17 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH19 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH21 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH23 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH25 : (JZ_non_alias < SM2_P_Z)) (PreH26 : (0 <= JZ_non_alias)) (PreH27 : (JY_non_alias < SM2_P_Z)) (PreH28 : (0 <= JY_non_alias)) (PreH29 : (JX_non_alias < SM2_P_Z)) (PreH30 : (0 <= JX_non_alias)) (PreH31 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_30_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH3 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH7 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH15 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH17 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH19 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH21 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH23 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH25 : (JZ_non_alias < SM2_P_Z)) (PreH26 : (0 <= JZ_non_alias)) (PreH27 : (JY_non_alias < SM2_P_Z)) (PreH28 : (0 <= JY_non_alias)) (PreH29 : (JX_non_alias < SM2_P_Z)) (PreH30 : (0 <= JX_non_alias)) (PreH31 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_30_non_alias := montg_double_jpoint_partial_solve_wit_30_non_alias_pure -> montg_double_jpoint_partial_solve_wit_30_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_31_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH4 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH6 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH10 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH12 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH14 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH16 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH18 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH20 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH22 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (JX_in_place)))) (PreH24 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH26 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH28 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH29 : (0 <= (mont_p (JY_in_place)))) (PreH30 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH31 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH32 : (JZ_in_place < SM2_P_Z)) (PreH33 : (0 <= JZ_in_place)) (PreH34 : (JY_in_place < SM2_P_Z)) (PreH35 : (0 <= JY_in_place)) (PreH36 : (JX_in_place < SM2_P_Z)) (PreH37 : (0 <= JX_in_place)) (PreH38 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH39 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_31_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH4 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH6 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH10 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH12 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH14 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH16 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH18 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH20 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH22 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (mont_p (JX_in_place)))) (PreH24 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH26 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH28 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH29 : (0 <= (mont_p (JY_in_place)))) (PreH30 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH31 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH32 : (JZ_in_place < SM2_P_Z)) (PreH33 : (0 <= JZ_in_place)) (PreH34 : (JY_in_place < SM2_P_Z)) (PreH35 : (0 <= JY_in_place)) (PreH36 : (JX_in_place < SM2_P_Z)) (PreH37 : (0 <= JX_in_place)) (PreH38 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH39 : (r_pre = a_pre)) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_31_in_place := montg_double_jpoint_partial_solve_wit_31_in_place_pure -> montg_double_jpoint_partial_solve_wit_31_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_32_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH4 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH6 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH10 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH12 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH14 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH16 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH18 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH20 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH22 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH24 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH26 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH28 : (JZ_non_alias < SM2_P_Z)) (PreH29 : (0 <= JZ_non_alias)) (PreH30 : (JY_non_alias < SM2_P_Z)) (PreH31 : (0 <= JY_non_alias)) (PreH32 : (JX_non_alias < SM2_P_Z)) (PreH33 : (0 <= JX_non_alias)) (PreH34 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_32_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : (&((r_pre)  # "JPoint" ->ₛ "x") = &((r_pre)  # "JPoint" ->ₛ "x"))) (PreH4 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH6 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH10 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH12 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH14 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH16 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH18 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH20 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH22 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH24 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH26 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH28 : (JZ_non_alias < SM2_P_Z)) (PreH29 : (0 <= JZ_non_alias)) (PreH30 : (JY_non_alias < SM2_P_Z)) (PreH31 : (0 <= JY_non_alias)) (PreH32 : (JX_non_alias < SM2_P_Z)) (PreH33 : (0 <= JX_non_alias)) (PreH34 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_32_non_alias := montg_double_jpoint_partial_solve_wit_32_non_alias_pure -> montg_double_jpoint_partial_solve_wit_32_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_33_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH7 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH15 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH17 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH19 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH21 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH23 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (mont_p (JX_in_place)))) (PreH25 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH27 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH29 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH30 : (0 <= (mont_p (JY_in_place)))) (PreH31 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH32 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH33 : (JZ_in_place < SM2_P_Z)) (PreH34 : (0 <= JZ_in_place)) (PreH35 : (JY_in_place < SM2_P_Z)) (PreH36 : (0 <= JY_in_place)) (PreH37 : (JX_in_place < SM2_P_Z)) (PreH38 : (0 <= JX_in_place)) (PreH39 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH40 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_33_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH5 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH7 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH9 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH11 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH13 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH15 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH17 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH19 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH21 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH23 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH24 : (0 <= (mont_p (JX_in_place)))) (PreH25 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH27 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH29 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH30 : (0 <= (mont_p (JY_in_place)))) (PreH31 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH32 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH33 : (JZ_in_place < SM2_P_Z)) (PreH34 : (0 <= JZ_in_place)) (PreH35 : (JY_in_place < SM2_P_Z)) (PreH36 : (0 <= JY_in_place)) (PreH37 : (JX_in_place < SM2_P_Z)) (PreH38 : (0 <= JX_in_place)) (PreH39 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH40 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
.

Definition montg_double_jpoint_partial_solve_wit_33_in_place := montg_double_jpoint_partial_solve_wit_33_in_place_pure -> montg_double_jpoint_partial_solve_wit_33_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_34_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH7 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH15 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH17 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH19 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH21 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH23 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH25 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH27 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH29 : (JZ_non_alias < SM2_P_Z)) (PreH30 : (0 <= JZ_non_alias)) (PreH31 : (JY_non_alias < SM2_P_Z)) (PreH32 : (0 <= JY_non_alias)) (PreH33 : (JX_non_alias < SM2_P_Z)) (PreH34 : (0 <= JX_non_alias)) (PreH35 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_34_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH5 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH6 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH7 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH8 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH9 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH10 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH11 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH12 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH13 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH14 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH15 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH16 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH17 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH18 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH19 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH20 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH21 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH22 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH23 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH24 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH25 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH26 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH27 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH28 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH29 : (JZ_non_alias < SM2_P_Z)) (PreH30 : (0 <= JZ_non_alias)) (PreH31 : (JY_non_alias < SM2_P_Z)) (PreH32 : (0 <= JY_non_alias)) (PreH33 : (JX_non_alias < SM2_P_Z)) (PreH34 : (0 <= JX_non_alias)) (PreH35 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "T" ) ) = ( &( "T" ) )) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_double_jpoint_partial_solve_wit_34_non_alias := montg_double_jpoint_partial_solve_wit_34_non_alias_pure -> montg_double_jpoint_partial_solve_wit_34_non_alias_aux.

Definition montg_double_jpoint_partial_solve_wit_35_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH10 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH12 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH14 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH16 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH18 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH20 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH22 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH24 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH26 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH27 : (0 <= (mont_p (JX_in_place)))) (PreH28 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH30 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH31 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH32 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH33 : (0 <= (mont_p (JY_in_place)))) (PreH34 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH35 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH36 : (JZ_in_place < SM2_P_Z)) (PreH37 : (0 <= JZ_in_place)) (PreH38 : (JY_in_place < SM2_P_Z)) (PreH39 : (0 <= JY_in_place)) (PreH40 : (JX_in_place < SM2_P_Z)) (PreH41 : (0 <= JX_in_place)) (PreH42 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH43 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "az" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_35_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH6 : ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) (PreH8 : ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place)))) (PreH10 : ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)))) (PreH12 : ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place)))) (PreH14 : ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place)))) (PreH16 : ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place)))) (PreH18 : ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place)))) (PreH20 : ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_t8 (JY_in_place)))) (PreH22 : ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_t16 (JY_in_place)))) (PreH24 : ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place)))) (PreH26 : ((mont_p (JX_in_place)) < SM2_P_Z)) (PreH27 : (0 <= (mont_p (JX_in_place)))) (PreH28 : ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_m4 (JY_in_place)))) (PreH30 : ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z)) (PreH31 : (0 <= (jdouble_trace_s2 (JY_in_place)))) (PreH32 : ((mont_p (JY_in_place)) < SM2_P_Z)) (PreH33 : (0 <= (mont_p (JY_in_place)))) (PreH34 : ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z)) (PreH35 : (0 <= (jdouble_trace_z2 (JZ_in_place)))) (PreH36 : (JZ_in_place < SM2_P_Z)) (PreH37 : (0 <= JZ_in_place)) (PreH38 : (JY_in_place < SM2_P_Z)) (PreH39 : (0 <= JY_in_place)) (PreH40 : (JX_in_place < SM2_P_Z)) (PreH41 : (0 <= JX_in_place)) (PreH42 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH43 : (r_pre = a_pre)) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_in_place)) )
|--
  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_u8 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_slope (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_prod (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_sum (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_diff (JX_in_place) (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_in_place) (JZ_in_place))) ” 
  &&  “ ((jdouble_trace_t8 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_t16 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s4 (JX_in_place) (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_in_place) (JY_in_place))) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((jdouble_trace_m4 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_in_place))) ” 
  &&  “ ((jdouble_trace_s2 (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_in_place)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_in_place) (JZ_in_place)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_in_place) (JY_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)))) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_in_place)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place ))) )
.

Definition montg_double_jpoint_partial_solve_wit_35_in_place := montg_double_jpoint_partial_solve_wit_35_in_place_pure -> montg_double_jpoint_partial_solve_wit_35_in_place_aux.

Definition montg_double_jpoint_partial_solve_wit_36_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH10 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH12 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH14 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH16 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH18 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH20 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH22 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH24 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH26 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH28 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH30 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH31 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH32 : (JZ_non_alias < SM2_P_Z)) (PreH33 : (0 <= JZ_non_alias)) (PreH34 : (JY_non_alias < SM2_P_Z)) (PreH35 : (0 <= JY_non_alias)) (PreH36 : (JX_non_alias < SM2_P_Z)) (PreH37 : (0 <= JX_non_alias)) (PreH38 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  ((( &( "rz" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ”
.

Definition montg_double_jpoint_partial_solve_wit_36_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH3 : (( &( "T" ) ) = ( &( "T" ) ))) (PreH4 : ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH5 : (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH6 : ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH7 : (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) (PreH8 : ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH9 : (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)))) (PreH10 : ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)))) (PreH12 : ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) (PreH14 : ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH15 : (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)))) (PreH16 : ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH17 : (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)))) (PreH18 : ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z)) (PreH19 : (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)))) (PreH20 : ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z)) (PreH21 : (0 <= (jdouble_trace_t8 (JY_non_alias)))) (PreH22 : ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z)) (PreH23 : (0 <= (jdouble_trace_t16 (JY_non_alias)))) (PreH24 : ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z)) (PreH25 : (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) (PreH26 : ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z)) (PreH27 : (0 <= (jdouble_trace_m4 (JY_non_alias)))) (PreH28 : ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z)) (PreH29 : (0 <= (jdouble_trace_s2 (JY_non_alias)))) (PreH30 : ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z)) (PreH31 : (0 <= (jdouble_trace_z2 (JZ_non_alias)))) (PreH32 : (JZ_non_alias < SM2_P_Z)) (PreH33 : (0 <= JZ_non_alias)) (PreH34 : (JY_non_alias < SM2_P_Z)) (PreH35 : (0 <= JY_non_alias)) (PreH36 : (JX_non_alias < SM2_P_Z)) (PreH37 : (0 <= JX_non_alias)) (PreH38 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) ,
  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_u8 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_slope (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_prod (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_sum (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_diff (JX_non_alias) (JZ_non_alias))) ” 
  &&  “ ((jdouble_trace_t8 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t8 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_t16 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_t16 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s4 (JX_non_alias) (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_m4 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_m4 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_s2 (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_s2 (JY_non_alias))) ” 
  &&  “ ((jdouble_trace_z2 (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (jdouble_trace_z2 (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_fp ( &( "T" ) ) (mont_p ((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp ( &( "U3" ) ) (mont_p ((jdouble_trace_t8 (JY_non_alias)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "U1" ) ) (mont_p ((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)))) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U2" ) ) (mont_p ((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)))) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "x") (mont_p ((jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (JX_non_alias)) )
  **  (store_fp ( &( "Zsqr" ) ) (mont_p ((jdouble_trace_z2 (JZ_non_alias)))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (JZ_non_alias)) )
  **  (store_fp &((r_pre)  # "JPoint" ->ₛ "z") (mont_p (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (JY_non_alias)) )
.

Definition montg_double_jpoint_partial_solve_wit_36_non_alias := montg_double_jpoint_partial_solve_wit_36_non_alias_pure -> montg_double_jpoint_partial_solve_wit_36_non_alias_aux.

Definition montg_double_jpoint_which_implies_wit_1 := 
(
forall (P_non_alias: ec_point) (a: Z) ,
  (store_mont_jpoint a P_non_alias )
|--
  EX (JX_non_alias: Z)  (JY_non_alias: Z)  (JZ_non_alias: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_mont_jpoint_coords a JX_non_alias JY_non_alias JZ_non_alias )
) \/
(
forall (P_non_alias: ec_point) (a: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_represents x y z P_non_alias )) ,
  (store_mont_jpoint_coords a x y z )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (JX_non_alias: Z)  (JY_non_alias: Z)  (JZ_non_alias: Z) ,
  “ ((mont_p (JX_non_alias)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (JX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_non_alias))) ” 
  &&  “ ((mont_p (JY_non_alias)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (JY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_non_alias))) ” 
  &&  “ ((mont_p (JZ_non_alias)) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (JZ_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JZ_non_alias))) ” 
  &&  “ (JZ_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JZ_non_alias) ” 
  &&  “ (JY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JY_non_alias) ” 
  &&  “ (JX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= JX_non_alias) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition montg_double_jpoint_which_implies_wit_2 := 
(
forall (P_in_place: ec_point) (a: Z) ,
  (store_mont_jpoint a P_in_place )
|--
  EX (JX_in_place: Z)  (JY_in_place: Z)  (JZ_in_place: Z) ,
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ”
  &&  (store_mont_jpoint_coords a JX_in_place JY_in_place JZ_in_place )
) \/
(
forall (P_in_place: ec_point) (a: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_represents x y z P_in_place )) ,
  (store_mont_jpoint_coords a x y z )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (JX_in_place: Z)  (JY_in_place: Z)  (JZ_in_place: Z) ,
  “ ((mont_p (JX_in_place)) = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((mont_p (JX_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JX_in_place))) ” 
  &&  “ ((mont_p (JY_in_place)) = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (JY_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JY_in_place))) ” 
  &&  “ ((mont_p (JZ_in_place)) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (JZ_in_place)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (JZ_in_place))) ” 
  &&  “ (JZ_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JZ_in_place) ” 
  &&  “ (JY_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JY_in_place) ” 
  &&  “ (JX_in_place < SM2_P_Z) ” 
  &&  “ (0 <= JX_in_place) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ”
  &&  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((a)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((a)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((a)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include jpoint_double_trace_Strategy_Correct.

Axiom proof_of_montg_double_jpoint_entail_wit_1_1_in_place : montg_double_jpoint_entail_wit_1_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_1_2_non_alias : montg_double_jpoint_entail_wit_1_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_2_in_place : montg_double_jpoint_entail_wit_2_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_3_1_in_place : montg_double_jpoint_entail_wit_3_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_3_2_non_alias : montg_double_jpoint_entail_wit_3_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_4_1_in_place : montg_double_jpoint_entail_wit_4_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_4_2_non_alias : montg_double_jpoint_entail_wit_4_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_5_1_in_place : montg_double_jpoint_entail_wit_5_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_5_2_non_alias : montg_double_jpoint_entail_wit_5_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_6_1_in_place : montg_double_jpoint_entail_wit_6_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_6_2_non_alias : montg_double_jpoint_entail_wit_6_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_7_1_in_place : montg_double_jpoint_entail_wit_7_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_7_2_non_alias : montg_double_jpoint_entail_wit_7_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_8_1_in_place : montg_double_jpoint_entail_wit_8_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_8_2_non_alias : montg_double_jpoint_entail_wit_8_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_9_1_in_place : montg_double_jpoint_entail_wit_9_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_9_2_non_alias : montg_double_jpoint_entail_wit_9_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_10_1_in_place : montg_double_jpoint_entail_wit_10_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_10_2_non_alias : montg_double_jpoint_entail_wit_10_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_11_1_in_place : montg_double_jpoint_entail_wit_11_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_11_2_non_alias : montg_double_jpoint_entail_wit_11_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_12_1_in_place : montg_double_jpoint_entail_wit_12_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_12_2_non_alias : montg_double_jpoint_entail_wit_12_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_13_1_in_place : montg_double_jpoint_entail_wit_13_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_13_2_non_alias : montg_double_jpoint_entail_wit_13_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_14_1_in_place : montg_double_jpoint_entail_wit_14_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_14_2_non_alias : montg_double_jpoint_entail_wit_14_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_15_1_in_place : montg_double_jpoint_entail_wit_15_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_15_2_non_alias : montg_double_jpoint_entail_wit_15_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_16_1_in_place : montg_double_jpoint_entail_wit_16_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_16_2_non_alias : montg_double_jpoint_entail_wit_16_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_17_1_in_place : montg_double_jpoint_entail_wit_17_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_17_2_non_alias : montg_double_jpoint_entail_wit_17_2_non_alias.
Axiom proof_of_montg_double_jpoint_entail_wit_18_1_in_place : montg_double_jpoint_entail_wit_18_1_in_place.
Axiom proof_of_montg_double_jpoint_entail_wit_18_2_non_alias : montg_double_jpoint_entail_wit_18_2_non_alias.
Axiom proof_of_montg_double_jpoint_return_wit_1_in_place : montg_double_jpoint_return_wit_1_in_place.
Axiom proof_of_montg_double_jpoint_return_wit_2_non_alias : montg_double_jpoint_return_wit_2_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_1_non_alias : montg_double_jpoint_partial_solve_wit_1_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_2_in_place : montg_double_jpoint_partial_solve_wit_2_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_3_in_place_pure : montg_double_jpoint_partial_solve_wit_3_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_3_in_place : montg_double_jpoint_partial_solve_wit_3_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_4_non_alias_pure : montg_double_jpoint_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_4_non_alias : montg_double_jpoint_partial_solve_wit_4_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_5_in_place_pure : montg_double_jpoint_partial_solve_wit_5_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_5_in_place : montg_double_jpoint_partial_solve_wit_5_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_6_non_alias_pure : montg_double_jpoint_partial_solve_wit_6_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_6_non_alias : montg_double_jpoint_partial_solve_wit_6_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_7_in_place_pure : montg_double_jpoint_partial_solve_wit_7_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_7_in_place : montg_double_jpoint_partial_solve_wit_7_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_8_non_alias_pure : montg_double_jpoint_partial_solve_wit_8_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_8_non_alias : montg_double_jpoint_partial_solve_wit_8_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_9_in_place_pure : montg_double_jpoint_partial_solve_wit_9_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_9_in_place : montg_double_jpoint_partial_solve_wit_9_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_10_non_alias_pure : montg_double_jpoint_partial_solve_wit_10_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_10_non_alias : montg_double_jpoint_partial_solve_wit_10_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_11_in_place_pure : montg_double_jpoint_partial_solve_wit_11_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_11_in_place : montg_double_jpoint_partial_solve_wit_11_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_12_non_alias_pure : montg_double_jpoint_partial_solve_wit_12_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_12_non_alias : montg_double_jpoint_partial_solve_wit_12_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_13_in_place_pure : montg_double_jpoint_partial_solve_wit_13_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_13_in_place : montg_double_jpoint_partial_solve_wit_13_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_14_non_alias_pure : montg_double_jpoint_partial_solve_wit_14_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_14_non_alias : montg_double_jpoint_partial_solve_wit_14_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_15_in_place_pure : montg_double_jpoint_partial_solve_wit_15_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_15_in_place : montg_double_jpoint_partial_solve_wit_15_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_16_non_alias_pure : montg_double_jpoint_partial_solve_wit_16_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_16_non_alias : montg_double_jpoint_partial_solve_wit_16_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_17_in_place_pure : montg_double_jpoint_partial_solve_wit_17_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_17_in_place : montg_double_jpoint_partial_solve_wit_17_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_18_non_alias_pure : montg_double_jpoint_partial_solve_wit_18_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_18_non_alias : montg_double_jpoint_partial_solve_wit_18_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_19_in_place_pure : montg_double_jpoint_partial_solve_wit_19_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_19_in_place : montg_double_jpoint_partial_solve_wit_19_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_20_non_alias_pure : montg_double_jpoint_partial_solve_wit_20_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_20_non_alias : montg_double_jpoint_partial_solve_wit_20_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_21_in_place_pure : montg_double_jpoint_partial_solve_wit_21_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_21_in_place : montg_double_jpoint_partial_solve_wit_21_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_22_non_alias_pure : montg_double_jpoint_partial_solve_wit_22_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_22_non_alias : montg_double_jpoint_partial_solve_wit_22_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_23_in_place_pure : montg_double_jpoint_partial_solve_wit_23_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_23_in_place : montg_double_jpoint_partial_solve_wit_23_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_24_non_alias_pure : montg_double_jpoint_partial_solve_wit_24_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_24_non_alias : montg_double_jpoint_partial_solve_wit_24_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_25_in_place_pure : montg_double_jpoint_partial_solve_wit_25_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_25_in_place : montg_double_jpoint_partial_solve_wit_25_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_26_non_alias_pure : montg_double_jpoint_partial_solve_wit_26_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_26_non_alias : montg_double_jpoint_partial_solve_wit_26_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_27_in_place_pure : montg_double_jpoint_partial_solve_wit_27_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_27_in_place : montg_double_jpoint_partial_solve_wit_27_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_28_non_alias_pure : montg_double_jpoint_partial_solve_wit_28_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_28_non_alias : montg_double_jpoint_partial_solve_wit_28_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_29_in_place_pure : montg_double_jpoint_partial_solve_wit_29_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_29_in_place : montg_double_jpoint_partial_solve_wit_29_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_30_non_alias_pure : montg_double_jpoint_partial_solve_wit_30_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_30_non_alias : montg_double_jpoint_partial_solve_wit_30_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_31_in_place_pure : montg_double_jpoint_partial_solve_wit_31_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_31_in_place : montg_double_jpoint_partial_solve_wit_31_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_32_non_alias_pure : montg_double_jpoint_partial_solve_wit_32_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_32_non_alias : montg_double_jpoint_partial_solve_wit_32_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_33_in_place_pure : montg_double_jpoint_partial_solve_wit_33_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_33_in_place : montg_double_jpoint_partial_solve_wit_33_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_34_non_alias_pure : montg_double_jpoint_partial_solve_wit_34_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_34_non_alias : montg_double_jpoint_partial_solve_wit_34_non_alias.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_35_in_place_pure : montg_double_jpoint_partial_solve_wit_35_in_place_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_35_in_place : montg_double_jpoint_partial_solve_wit_35_in_place.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_36_non_alias_pure : montg_double_jpoint_partial_solve_wit_36_non_alias_pure.
Axiom proof_of_montg_double_jpoint_partial_solve_wit_36_non_alias : montg_double_jpoint_partial_solve_wit_36_non_alias.
Axiom proof_of_montg_double_jpoint_which_implies_wit_1 : montg_double_jpoint_which_implies_wit_1.
Axiom proof_of_montg_double_jpoint_which_implies_wit_2 : montg_double_jpoint_which_implies_wit_2.

End VC_Correct.
