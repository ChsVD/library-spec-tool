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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_double_jpoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import montg_double_jpoint_proof_auto.
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

Lemma proof_of_montg_double_jpoint_return_wit_1_in_place : montg_double_jpoint_return_wit_1_in_place.
Proof.
  unfold montg_double_jpoint_return_wit_1_in_place.
  right; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (jpoint_double_point_of_trace
    JX_in_place JY_in_place JZ_in_place P_in_place PreH43) as Hresult.
  Exists ((jdouble_trace_s2 JY_in_place * JZ_in_place) mod SM2_P_Z)
    (jdouble_trace_ry JX_in_place JY_in_place JZ_in_place)
    (jdouble_trace_rx JX_in_place JY_in_place JZ_in_place).
  entailer!.
  all: first
    [ rewrite mont_p_mod; reflexivity
    | apply Z.mod_pos_bound;
      pose proof sm2_p_montgomery_bounds; lia ].
Qed. 

Lemma proof_of_montg_double_jpoint_return_wit_2_non_alias : montg_double_jpoint_return_wit_2_non_alias.
Proof.
  unfold montg_double_jpoint_return_wit_2_non_alias.
  right; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (jpoint_double_point_of_trace
    JX_non_alias JY_non_alias JZ_non_alias P_non_alias PreH39) as Hresult.
  Exists ((jdouble_trace_s2 JY_non_alias * JZ_non_alias) mod SM2_P_Z)
    (jdouble_trace_ry JX_non_alias JY_non_alias JZ_non_alias)
    (jdouble_trace_rx JX_non_alias JY_non_alias JZ_non_alias)
    JZ_non_alias JY_non_alias JX_non_alias.
  entailer!.
  all: first
    [ rewrite mont_p_mod; reflexivity
    | apply Z.mod_pos_bound;
      pose proof sm2_p_montgomery_bounds; lia ].
Qed. 

Lemma proof_of_montg_double_jpoint_partial_solve_wit_15_in_place_pure_split_goal_1 : montg_double_jpoint_partial_solve_wit_15_in_place_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  Intros.
  sep_apply (store_u256_undef_neq (&("T")) (&("U3"))
    (mont_p (jdouble_trace_t16 JY_in_place))).
  entailer!.
Qed.

Lemma proof_of_montg_double_jpoint_partial_solve_wit_15_in_place_pure : montg_double_jpoint_partial_solve_wit_15_in_place_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  Intros.
  sep_apply (store_u256_undef_neq (&("T")) (&("U3"))
    (mont_p (jdouble_trace_t16 JY_in_place))).
  entailer!.
Qed. 

Lemma proof_of_montg_double_jpoint_partial_solve_wit_16_non_alias_pure_split_goal_1 : montg_double_jpoint_partial_solve_wit_16_non_alias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  Intros.
  sep_apply (store_u256_undef_neq (&("T")) (&("U3"))
    (mont_p (jdouble_trace_t16 JY_non_alias))).
  entailer!.
Qed.

Lemma proof_of_montg_double_jpoint_partial_solve_wit_16_non_alias_pure : montg_double_jpoint_partial_solve_wit_16_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_fp, store_mod.
  Intros.
  sep_apply (store_u256_undef_neq (&("T")) (&("U3"))
    (mont_p (jdouble_trace_t16 JY_non_alias))).
  entailer!.
Qed. 

Lemma proof_of_montg_double_jpoint_which_implies_wit_1 : montg_double_jpoint_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_montg_double_jpoint_which_implies_wit_2 : montg_double_jpoint_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 
