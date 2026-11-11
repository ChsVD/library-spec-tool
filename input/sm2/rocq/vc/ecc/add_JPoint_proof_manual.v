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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_proof_auto.
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
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Local Open Scope sac.

Lemma proof_of_add_JPoint_entail_wit_27_1_non_alias_split_goal_1 : add_JPoint_entail_wit_27_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold aj_generic_trace_case; tauto.
Qed.

Lemma proof_of_add_JPoint_entail_wit_27_1_non_alias : add_JPoint_entail_wit_27_1_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_JPoint_entail_wit_27_1_non_alias_split_goal_1.
Qed. 

Lemma proof_of_add_JPoint_entail_wit_27_2_non_alias_split_goal_1 : add_JPoint_entail_wit_27_2_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold aj_generic_trace_case; tauto.
Qed.

Lemma proof_of_add_JPoint_entail_wit_27_2_non_alias : add_JPoint_entail_wit_27_2_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_JPoint_entail_wit_27_2_non_alias_split_goal_1.
Qed. 

Lemma proof_of_add_JPoint_entail_wit_28_1_r_eq_point1_split_goal_1 : add_JPoint_entail_wit_28_1_r_eq_point1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold aj_generic_trace_case; tauto.
Qed.

Lemma proof_of_add_JPoint_entail_wit_28_1_r_eq_point1 : add_JPoint_entail_wit_28_1_r_eq_point1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_JPoint_entail_wit_28_1_r_eq_point1_split_goal_1.
Qed. 

Lemma proof_of_add_JPoint_entail_wit_28_2_r_eq_point1_split_goal_1 : add_JPoint_entail_wit_28_2_r_eq_point1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold aj_generic_trace_case; tauto.
Qed.

Lemma proof_of_add_JPoint_entail_wit_28_2_r_eq_point1 : add_JPoint_entail_wit_28_2_r_eq_point1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_JPoint_entail_wit_28_2_r_eq_point1_split_goal_1.
Qed. 

Lemma proof_of_add_JPoint_return_wit_1_non_alias : add_JPoint_return_wit_1_non_alias.
Proof.
  unfold add_JPoint_return_wit_1_non_alias.
  right; intros.
  pose proof (aj_same_u_s_sum_zero_adds_infinity
    X1_non_alias Y1_non_alias Z1_non_alias X2_non_alias Y2_non_alias Z2_non_alias
    P1_non_alias P2_non_alias
    PreH34 PreH32 PreH30 PreH31 PreH19 PreH14) as Hadd.
  destruct
    SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.canonical_infinity_representation
    as [Hinf_rep Hinf_encoding].
  assert (Hone : 0 <= 1 < SM2_P_Z)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (Hzero : 0 <= 0 < SM2_P_Z)
    by (pose proof sm2_p_montgomery_bounds; lia).
  Exists 0 1 1 Z2_non_alias Y2_non_alias X2_non_alias
         Z1_non_alias Y1_non_alias X1_non_alias.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH3, PreH6, PreH9.
  sep_apply (aj_jpoint_field_limbs_pack result_pre "x" 1 Hone).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "y" 1 Hone).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "z" 0 Hzero).
  sep_apply (aj_global_jpoint_field_limbs_pack "x" 1 Hone).
  sep_apply (aj_global_jpoint_field_limbs_pack "y" 1 Hone).
  sep_apply (aj_global_jpoint_field_limbs_pack "z" 0 Hzero).
  rewrite Hadd.
  unfold store_jpoint_zero, store_jpoint_fields;
    entailer!; csimpl; entailer!.
Qed. 

Lemma proof_of_add_JPoint_return_wit_2_r_eq_point1 : add_JPoint_return_wit_2_r_eq_point1.
Proof.
  unfold add_JPoint_return_wit_2_r_eq_point1.
  right; intros.
  pose proof (aj_same_u_s_sum_zero_adds_infinity
    X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
    X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1
    P1_r_eq_point1 P2_r_eq_point1
    PreH34 PreH32 PreH30 PreH31 PreH19 PreH14) as Hadd.
  destruct
    SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.canonical_infinity_representation
    as [Hinf_rep Hinf_encoding].
  assert (Hone : 0 <= 1 < SM2_P_Z)
    by (pose proof sm2_p_montgomery_bounds; lia).
  assert (Hzero : 0 <= 0 < SM2_P_Z)
    by (pose proof sm2_p_montgomery_bounds; lia).
  Exists 0 1 1
         Z2_r_eq_point1 Y2_r_eq_point1 X2_r_eq_point1.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH3, PreH6, PreH9.
  sep_apply (aj_jpoint_field_limbs_pack result_pre "x" 1 Hone).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "y" 1 Hone).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "z" 0 Hzero).
  sep_apply (aj_global_jpoint_field_limbs_pack "x" 1 Hone).
  sep_apply (aj_global_jpoint_field_limbs_pack "y" 1 Hone).
  sep_apply (aj_global_jpoint_field_limbs_pack "z" 0 Hzero).
  rewrite Hadd.
  unfold store_jpoint_zero, store_jpoint_fields;
    entailer!; csimpl; entailer!.
Qed. 

Lemma proof_of_add_JPoint_return_wit_3_non_alias : add_JPoint_return_wit_3_non_alias.
Proof.
  unfold add_JPoint_return_wit_3_non_alias.
  right; intros.
  pose proof PreH12 as Hbounds.
  destruct Hbounds as [Hx [Hy [Hz Hrest]]].
  sep_apply (aj_copy_full_lists_to_two_jpoint_fields
    result_pre point1_pre
    copy_xs_non_alias copy_ys_non_alias copy_zs_non_alias
    X1_non_alias Y1_non_alias Z1_non_alias
    PreH3 PreH6 PreH9 Hx Hy Hz).
  Exists Z1_non_alias Y1_non_alias X1_non_alias
         Z1_non_alias Y1_non_alias X1_non_alias.
  rewrite PreH17, sm2_point_add_infinity_right.
  unfold store_jpoint_fields; entailer!.
  all: rewrite <- PreH17; assumption.
Qed. 

Lemma proof_of_add_JPoint_return_wit_4_r_eq_point1_split_goal_1 : add_JPoint_return_wit_4_r_eq_point1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite sm2_point_add_infinity_right; exact PreH3.
Qed.

Lemma proof_of_add_JPoint_return_wit_4_r_eq_point1_split_goal_2 : add_JPoint_return_wit_4_r_eq_point1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite sm2_point_add_infinity_right; exact PreH4.
Qed.

Lemma proof_of_add_JPoint_return_wit_4_r_eq_point1 : add_JPoint_return_wit_4_r_eq_point1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_add_JPoint_return_wit_4_r_eq_point1_split_goal_1.
  - Goal_apply proof_of_add_JPoint_return_wit_4_r_eq_point1_split_goal_2.
Qed. 

Lemma proof_of_add_JPoint_return_wit_5_non_alias : add_JPoint_return_wit_5_non_alias.
Proof.
  unfold add_JPoint_return_wit_5_non_alias.
  right; intros.
  pose proof PreH10 as Hbounds.
  destruct Hbounds as [Hx [Hy [Hz Hrest]]].
  sep_apply (aj_copy_full_lists_to_two_jpoint_fields
    result_pre point2_pre
    copy_xs_non_alias copy_ys_non_alias copy_zs_non_alias
    X2_non_alias Y2_non_alias Z2_non_alias
    PreH3 PreH6 PreH9 Hx Hy Hz).
  Exists Z2_non_alias Y2_non_alias X2_non_alias
         Z2_non_alias Y2_non_alias X2_non_alias.
  rewrite PreH17, sm2_point_add_infinity_left.
  unfold store_jpoint_fields; entailer!.
  all: rewrite <- PreH17; assumption.
Qed. 

Lemma proof_of_add_JPoint_return_wit_6_r_eq_point1 : add_JPoint_return_wit_6_r_eq_point1.
Proof.
  unfold add_JPoint_return_wit_6_r_eq_point1.
  right; intros.
  pose proof PreH10 as Hbounds.
  destruct Hbounds as [Hx [Hy [Hz Hrest]]].
  sep_apply (aj_copy_full_lists_to_two_jpoint_fields
    result_pre point2_pre
    copy_xs_r_eq_point1 copy_ys_r_eq_point1 copy_zs_r_eq_point1
    X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1
    PreH3 PreH6 PreH9 Hx Hy Hz).
  Exists Z2_r_eq_point1 Y2_r_eq_point1 X2_r_eq_point1
         Z2_r_eq_point1 Y2_r_eq_point1 X2_r_eq_point1.
  rewrite PreH17, sm2_point_add_infinity_left.
  unfold store_jpoint_fields; entailer!.
Qed. 

Lemma proof_of_add_JPoint_return_wit_7_r_eq_point1 : add_JPoint_return_wit_7_r_eq_point1.
Proof.
  unfold add_JPoint_return_wit_7_r_eq_point1.
  right; intros.
  pose proof (aj_same_u_same_s_points_equal
    X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
    X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1
    P1_r_eq_point1 P2_r_eq_point1
    PreH16 PreH14 PreH12 PreH13 PreH11 PreH6) as Hpoints.
  subst P2_r_eq_point1.
  unfold store_jpoint_with_canonical_infinity.
  Intros rx ry rz.
  Exists rz ry rx
         Z2_r_eq_point1 Y2_r_eq_point1 X2_r_eq_point1.
  unfold sm2_point_double in *.
  unfold store_jpoint_fields.
  entailer!.
  unfold store_jpoint_zero, store_jpoint_fields; entailer!.
  csimpl; entailer!.
Qed. 

Lemma proof_of_add_JPoint_return_wit_8_non_alias : add_JPoint_return_wit_8_non_alias.
Proof.
  unfold add_JPoint_return_wit_8_non_alias.
  right; intros.
  pose proof (aj_same_u_same_s_points_equal
    X1_non_alias Y1_non_alias Z1_non_alias X2_non_alias Y2_non_alias Z2_non_alias
    P1_non_alias P2_non_alias
    PreH15 PreH13 PreH11 PreH12 PreH10 PreH5) as Hpoints.
  subst P2_non_alias.
  unfold store_jpoint_with_canonical_infinity.
  Intros rx ry rz.
  Exists rz ry rx Z2_non_alias Y2_non_alias X2_non_alias.
  unfold sm2_point_double in *.
  unfold store_jpoint_fields.
  entailer!.
  unfold store_jpoint_zero, store_jpoint_fields; entailer!.
  csimpl; entailer!.
Qed. 

Lemma proof_of_add_JPoint_return_wit_9_non_alias : add_JPoint_return_wit_9_non_alias.
Proof.
  unfold add_JPoint_return_wit_9_non_alias.
  right; intros.
  exfalso.
  apply PreH21.
  eapply aj_same_u_different_s_implies_s_sum_zero; eauto.
Qed. 

Lemma proof_of_add_JPoint_return_wit_10_r_eq_point1 : add_JPoint_return_wit_10_r_eq_point1.
Proof.
  unfold add_JPoint_return_wit_10_r_eq_point1.
  right; intros.
  exfalso.
  apply PreH21.
  eapply aj_same_u_different_s_implies_s_sum_zero; eauto.
Qed. 

Lemma proof_of_add_JPoint_return_wit_11_non_alias : add_JPoint_return_wit_11_non_alias.
Proof.
  unfold add_JPoint_return_wit_11_non_alias.
  right; intros.
  pose proof (aj_result_refines_finite_distinct
    X1_non_alias Y1_non_alias Z1_non_alias X2_non_alias Y2_non_alias Z2_non_alias
    P1_non_alias P2_non_alias
    PreH31 PreH29 PreH21 PreH27 PreH28) as Hrefines.
  destruct Hrefines as [Hresult_rep Hresult_encoding].
  pose proof Hresult_rep as Hresult_rep_bounds.
  destruct Hresult_rep_bounds as [Hrx [Hry [Hrz Hrest]]].
  Exists
    (aj_rz X1_non_alias Z1_non_alias X2_non_alias Z2_non_alias)
    (aj_ry X1_non_alias Y1_non_alias Z1_non_alias
           X2_non_alias Y2_non_alias Z2_non_alias)
    (aj_rx X1_non_alias Y1_non_alias Z1_non_alias
           X2_non_alias Y2_non_alias Z2_non_alias)
    Z2_non_alias Y2_non_alias X2_non_alias
    Z1_non_alias Y1_non_alias X1_non_alias.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH11, PreH6, PreH1.
  sep_apply (aj_jpoint_field_limbs_pack result_pre "x"
    (aj_rx X1_non_alias Y1_non_alias Z1_non_alias X2_non_alias Y2_non_alias Z2_non_alias) Hrx).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "y"
    (aj_ry X1_non_alias Y1_non_alias Z1_non_alias X2_non_alias Y2_non_alias Z2_non_alias) Hry).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "z"
    (aj_rz X1_non_alias Z1_non_alias X2_non_alias Z2_non_alias) Hrz).
  repeat rewrite Zsublist_nil by lia.
  cbn [UInt64Array.full store_array store_array_rec].
  entailer!.
  unfold store_jpoint_zero, store_jpoint_fields; entailer!.
  csimpl; entailer!.
Qed. 

Lemma proof_of_add_JPoint_return_wit_12_r_eq_point1 : add_JPoint_return_wit_12_r_eq_point1.
Proof.
  unfold add_JPoint_return_wit_12_r_eq_point1.
  right; intros.
  pose proof (aj_result_refines_finite_distinct
    X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
    X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1
    P1_r_eq_point1 P2_r_eq_point1
    PreH31 PreH29 PreH21 PreH27 PreH28) as Hrefines.
  destruct Hrefines as [Hresult_rep Hresult_encoding].
  pose proof Hresult_rep as Hresult_rep_bounds.
  destruct Hresult_rep_bounds as [Hrx [Hry [Hrz Hrest]]].
  Exists
    (aj_rz X1_r_eq_point1 Z1_r_eq_point1
           X2_r_eq_point1 Z2_r_eq_point1)
    (aj_ry X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
           X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1)
    (aj_rx X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
           X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1)
    Z2_r_eq_point1 Y2_r_eq_point1 X2_r_eq_point1.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH11, PreH6, PreH1.
  sep_apply (aj_jpoint_field_limbs_pack result_pre "x"
    (aj_rx X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
           X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1) Hrx).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "y"
    (aj_ry X1_r_eq_point1 Y1_r_eq_point1 Z1_r_eq_point1
           X2_r_eq_point1 Y2_r_eq_point1 Z2_r_eq_point1) Hry).
  sep_apply (aj_jpoint_field_limbs_pack result_pre "z"
    (aj_rz X1_r_eq_point1 Z1_r_eq_point1 X2_r_eq_point1 Z2_r_eq_point1) Hrz).
  repeat rewrite Zsublist_nil by lia.
  cbn [UInt64Array.full store_array store_array_rec].
  entailer!.
  unfold store_jpoint_zero, store_jpoint_fields; entailer!.
  csimpl; entailer!.
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_1 : add_JPoint_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_2 : add_JPoint_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_3 : add_JPoint_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_4 : add_JPoint_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_7 : add_JPoint_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_8 : add_JPoint_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_9 : add_JPoint_which_implies_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_10 : add_JPoint_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_12 : add_JPoint_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_13 : add_JPoint_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_14 : add_JPoint_which_implies_wit_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_JPoint_which_implies_wit_15 : add_JPoint_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_u32_eq_zero_derive_fp_by_base : u32_eq_zero_derive_fp_by_base.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename A_fp into A.
  unfold store_fp, store_mod.
  Intros.
  Exists A.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    entailer!.
    apply derivable1_orp_elim.
    + Intros retval.
      Left.
      Exists retval.
      entailer!.
    + Intros retval.
      Right.
      Exists retval.
      entailer!.
Qed. 

Lemma proof_of_u32_eq_derive_fp_by_base : u32_eq_derive_fp_by_base.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename B_fp into B.
  rename A_fp into A.
  unfold store_fp, store_mod.
  Intros.
  Exists A B.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    entailer!.
    apply derivable1_orp_elim.
    + Intros retval.
      Left.
      Exists retval.
      entailer!.
    + Intros retval.
      Right.
      Exists retval.
      entailer!.
Qed. 
