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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_and_AFPoint_def.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_and_AFPoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_and_AFPoint_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.add_JPoint_and_AFPoint_lib.
Local Open Scope sac.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1_split_goal_spatial : add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst result_pre P2_impl_r_eq_point1.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec P1_impl_r_eq_point1 ECInfinity);
    [contradiction |].
  destruct (sm2_ec_point_dec ECInfinity ECInfinity);
    [| contradiction].
  rewrite sm2_point_add_infinity_right; entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1 : add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst result_pre P2_impl_r_eq_point1.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec P1_impl_r_eq_point1 ECInfinity);
    [contradiction |].
  destruct (sm2_ec_point_dec ECInfinity ECInfinity);
    [| contradiction].
  rewrite sm2_point_add_infinity_right.
  entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_1 : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  destruct PreH1 as [HJX [HJY [HJZ Htail]]]; lia.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_2 : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  destruct PreH1 as [HJX [HJY [HJZ Htail]]]; lia.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_3 : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  destruct PreH1 as [HJX [HJY [HJZ Htail]]]; lia.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_4 : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  destruct PreH1 as [HJX [HJY [HJZ Htail]]]; lia.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_5 : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  destruct PreH1 as [HJX [HJY [HJZ Htail]]]; lia.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_6 : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  entailer!.
  destruct PreH1 as [HJX [HJY [HJZ Htail]]]; lia.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_spatial : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH1 as Hrep_all.
  destruct PreH1 as [HJXb [HJYb [HJZb Hrepr_tail]]].
  subst P2_impl_non_alias.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec P1_impl_non_alias ECInfinity);
    [contradiction |].
  destruct (sm2_ec_point_dec ECInfinity ECInfinity); [| contradiction].
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH5, PreH8, PreH11.
  rewrite sm2_point_add_infinity_right.
  unfold store_jpoint_with_canonical_infinity, store_jpoint_fields,
    store_fp, store_mod, store_u256.
  Exists JX JY JZ.
  entailer!.
  csimpl; entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH1 as Hrep_all.
  destruct PreH1 as [HJXb [HJYb [HJZb Hrepr_tail]]].
  subst P2_impl_non_alias.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec P1_impl_non_alias ECInfinity);
    [contradiction |].
  destruct (sm2_ec_point_dec ECInfinity ECInfinity);
    [| contradiction].
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  rewrite PreH5, PreH8, PreH11.
  rewrite sm2_point_add_infinity_right.
  unfold store_jpoint_with_canonical_infinity,
    store_jpoint_fields, store_fp, store_mod, store_u256.
  Exists JX JY JZ JX JY JZ.
  assert (Hp1x :
    &(point1_pre # "JPoint" ->ₛ "x" .ₛ "v") =
    &(((&(point1_pre # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hp1y :
    &(point1_pre # "JPoint" ->ₛ "y" .ₛ "v") =
    &(((&(point1_pre # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hp1z :
    &(point1_pre # "JPoint" ->ₛ "z" .ₛ "v") =
    &(((&(point1_pre # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hrx :
    &(result_pre # "JPoint" ->ₛ "x" .ₛ "v") =
    &(((&(result_pre # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hry :
    &(result_pre # "JPoint" ->ₛ "y" .ₛ "v") =
    &(((&(result_pre # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  assert (Hrz :
    &(result_pre # "JPoint" ->ₛ "z" .ₛ "v") =
    &(((&(result_pre # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v")).
  { csimpl. reflexivity. }
  rewrite Hp1x, Hp1y, Hp1z, Hrx, Hry, Hrz.
  entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_3_impl_non_alias_split_goal_spatial : add_JPoint_and_AFPoint_return_wit_3_impl_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst P1_impl_non_alias.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec ECInfinity ECInfinity); [| contradiction].
  rewrite sm2_point_add_infinity_left; entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_3_impl_non_alias : add_JPoint_and_AFPoint_return_wit_3_impl_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst P1_impl_non_alias.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec ECInfinity ECInfinity);
    [| contradiction].
  rewrite sm2_point_add_infinity_left.
  entailer!.
  unfold store_jpoint_with_canonical_infinity.
  Exists x y z; entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1_split_goal_spatial : add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst result_pre P1_impl_r_eq_point1.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec ECInfinity ECInfinity); [| contradiction].
  rewrite sm2_point_add_infinity_left; entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst result_pre P1_impl_r_eq_point1.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec ECInfinity ECInfinity);
    [| contradiction].
  rewrite sm2_point_add_infinity_left.
  entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_5_impl_non_alias_split_goal_spatial : add_JPoint_and_AFPoint_return_wit_5_impl_non_alias_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (Z2 := Zmod (z * z) SM2_P_Z).
  set (A := Zmod (Zmod (x_2 * Z2) SM2_P_Z - x) SM2_P_Z).
  set (B := Zmod
    (Zmod (Zmod (y_2 * Z2) SM2_P_Z * z) SM2_P_Z - y) SM2_P_Z).
  set (C2 := Zmod (A * A) SM2_P_Z).
  set (C3 := Zmod (C2 * A) SM2_P_Z).
  set (X1C2 := Zmod (x * C2) SM2_P_Z).
  set (D2 := Zmod (B * B) SM2_P_Z).
  set (X1C22 := Zmod (X1C2 + X1C2) SM2_P_Z).
  set (RX := Zmod (Zmod (D2 - X1C22) SM2_P_Z - C3) SM2_P_Z).
  set (TMP := Zmod (X1C2 - RX) SM2_P_Z).
  set (RY := Zmod
    (Zmod (B * TMP) SM2_P_Z - Zmod (y * C3) SM2_P_Z) SM2_P_Z).
  set (RZ := Zmod (z * A) SM2_P_Z).
  assert (Hp : 0 < SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  assert (Hneq : P1_impl_non_alias <> P2_impl_non_alias)
    by (apply PreH16; tauto).
  assert (Ha : 0 <= A < SM2_P_Z)
    by (unfold A, Zmod; apply Z.mod_pos_bound; lia).
  assert (Hrx : 0 <= RX < SM2_P_Z)
    by (unfold RX, Zmod; apply Z.mod_pos_bound; lia).
  assert (Hry : 0 <= RY < SM2_P_Z)
    by (unfold RY, Zmod; apply Z.mod_pos_bound; lia).
  assert (Hrz : 0 <= RZ < SM2_P_Z)
    by (unfold RZ, Zmod; apply Z.mod_pos_bound; lia).
  pose proof (jpoint_add_afpoint_mixed_mod_represents
    P1_impl_non_alias P2_impl_non_alias
    x y z x_2 y_2 Z2 A B C2 C3 X1C2 D2 X1C22 RX TMP RY RZ
    PreH15 PreH11 Hneq PreH7 PreH5 Ha Hrx Hry Hrz
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as HRrep.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec P1_impl_non_alias ECInfinity);
    [contradiction |].
  destruct (sm2_ec_point_dec P2_impl_non_alias ECInfinity);
    [contradiction |].
  unfold store_jpoint.
  Exists RX RY RZ.
  unfold store_jpoint_fields.
  entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_5_impl_non_alias : add_JPoint_and_AFPoint_return_wit_5_impl_non_alias.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_JPoint_and_AFPoint_return_wit_5_impl_non_alias_split_goal_spatial.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1_split_goal_spatial : add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (Z2 := Zmod (z * z) SM2_P_Z).
  set (A := Zmod (Zmod (x_2 * Z2) SM2_P_Z - x) SM2_P_Z).
  set (B := Zmod
    (Zmod (Zmod (y_2 * Z2) SM2_P_Z * z) SM2_P_Z - y) SM2_P_Z).
  set (C2 := Zmod (A * A) SM2_P_Z).
  set (C3 := Zmod (C2 * A) SM2_P_Z).
  set (X1C2 := Zmod (x * C2) SM2_P_Z).
  set (D2 := Zmod (B * B) SM2_P_Z).
  set (X1C22 := Zmod (X1C2 + X1C2) SM2_P_Z).
  set (RX := Zmod (Zmod (D2 - X1C22) SM2_P_Z - C3) SM2_P_Z).
  set (TMP := Zmod (X1C2 - RX) SM2_P_Z).
  set (RY := Zmod
    (Zmod (B * TMP) SM2_P_Z - Zmod (y * C3) SM2_P_Z) SM2_P_Z).
  set (RZ := Zmod (z * A) SM2_P_Z).
  assert (Hp : 0 < SM2_P_Z) by (pose proof sm2_p_gt_one; lia).
  assert (Hneq : P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)
    by (apply PreH18; tauto).
  assert (Ha : 0 <= A < SM2_P_Z)
    by (unfold A, Zmod; apply Z.mod_pos_bound; lia).
  assert (Hrx : 0 <= RX < SM2_P_Z)
    by (unfold RX, Zmod; apply Z.mod_pos_bound; lia).
  assert (Hry : 0 <= RY < SM2_P_Z)
    by (unfold RY, Zmod; apply Z.mod_pos_bound; lia).
  assert (Hrz : 0 <= RZ < SM2_P_Z)
    by (unfold RZ, Zmod; apply Z.mod_pos_bound; lia).
  pose proof (jpoint_add_afpoint_mixed_mod_represents
    P1_impl_r_eq_point1 P2_impl_r_eq_point1
    x y z x_2 y_2 Z2 A B C2 C3 X1C2 D2 X1C22 RX TMP RY RZ
    PreH16 PreH12 Hneq PreH8 PreH6 Ha Hrx Hry Hrz
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as HRrep.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec P1_impl_r_eq_point1 ECInfinity);
    [contradiction |].
  destruct (sm2_ec_point_dec P2_impl_r_eq_point1 ECInfinity);
    [contradiction |].
  unfold store_jpoint.
  Exists RX RY RZ.
  unfold store_jpoint_fields.
  entailer!.
Qed.

Lemma proof_of_add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1 : add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1_split_goal_spatial.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_which_implies_wit_1 : add_JPoint_and_AFPoint_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_jpoint_with_canonical_infinity.
  Intros JX JY JZ.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256,
    store_u256_limbs.
  Intros jx0 jx1 jx2 jx3 jy0 jy1 jy2 jy3 jz0 jz1 jz2 jz3.
  Exists (jz0 :: jz1 :: jz2 :: jz3 :: nil)
    (jy0 :: jy1 :: jy2 :: jy3 :: nil)
    (jx0 :: jx1 :: jx2 :: jx3 :: nil)
    JX JY JZ.
  unfold StructPredJPoint, StructPredu32,
    UndefStructPredJPoint, UndefStructPredu32.
  cbn [JPoint_x JPoint_y JPoint_z u32_v].
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  split_pure_spatial.
  - rewrite !sizeof_uint64.
    cbn.
    assert (Hrxaddr :
      &(result # "JPoint" ->ₛ "x" .ₛ "v") =
      &(((&(result # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v")).
    { csimpl. reflexivity. }
    assert (Hryaddr :
      &(result # "JPoint" ->ₛ "y" .ₛ "v") =
      &(((&(result # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v")).
    { csimpl. reflexivity. }
    assert (Hrzaddr :
      &(result # "JPoint" ->ₛ "z" .ₛ "v") =
      &(((&(result # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v")).
    { csimpl. reflexivity. }
    rewrite Hrxaddr, Hryaddr, Hrzaddr.
    cancel.
    cancel.
    cancel.
  - destruct H as [Hrep Hcanon].
    destruct H3 as [Hjx0 [Hjx1 [Hjx2 [Hjx3 HJX]]]].
    destruct H4 as [Hjy0 [Hjy1 [Hjy2 [Hjy3 HJY]]]].
    destruct H5 as [Hjz0 [Hjz1 [Hjz2 [Hjz3 HJZ]]]].
    assert (HBx :
      u64_list_bounded (jx0 :: jx1 :: jx2 :: jx3 :: nil)).
    {
      unfold u64_list_bounded, limb_list_bounded.
      intros i Hi.
      apply ZRange.Forall_Znth_Zlength.
      - repeat constructor; tauto.
      - exact Hi.
    }
    assert (HBy :
      u64_list_bounded (jy0 :: jy1 :: jy2 :: jy3 :: nil)).
    {
      unfold u64_list_bounded, limb_list_bounded.
      intros i Hi.
      apply ZRange.Forall_Znth_Zlength.
      - repeat constructor; tauto.
      - exact Hi.
    }
    assert (HBz :
      u64_list_bounded (jz0 :: jz1 :: jz2 :: jz3 :: nil)).
    {
      unfold u64_list_bounded, limb_list_bounded.
      intros i Hi.
      apply ZRange.Forall_Znth_Zlength.
      - repeat constructor; tauto.
      - exact Hi.
    }
    assert (HVx :
      u64_list_value (jx0 :: jx1 :: jx2 :: jx3 :: nil) = JX).
    { rewrite u64_list_value_four. symmetry. exact HJX. }
    assert (HVy :
      u64_list_value (jy0 :: jy1 :: jy2 :: jy3 :: nil) = JY).
    { rewrite u64_list_value_four. symmetry. exact HJY. }
    assert (HVz :
      u64_list_value (jz0 :: jz1 :: jz2 :: jz3 :: nil) = JZ).
    { rewrite u64_list_value_four. symmetry. exact HJZ. }
    unfold jpoint_canonical_infinity_encoding.
    entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_derive_canonical_r_eq_point1_by_impl_r_eq_point1 : add_JPoint_and_AFPoint_derive_canonical_r_eq_point1_by_impl_r_eq_point1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P2_canonical_r_eq_point1 into P2.
  rename P1_canonical_r_eq_point1 into P1.
  repeat apply derivable1_orp_elim;
    Intros;
    Exists P1 P2;
    apply sepcon_cancel_end.
  all: try entailer!.
  all: apply derivable1_wand_sepcon_adjoint; Intros.
  all: sep_apply
    (store_mixed_add_result_impl_is_canonical
      result_pre P1 P2 ltac:(tauto)).
  all: entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_derive_r_eq_point1_by_impl_r_eq_point1 : add_JPoint_and_AFPoint_derive_r_eq_point1_by_impl_r_eq_point1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P2_r_eq_point1 into P2.
  rename P1_r_eq_point1 into P1.
  Exists P1 P2.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros.
    sep_apply
      (store_mixed_add_result_impl_forget result_pre P1 P2).
    entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_derive_canonical_non_alias_by_impl_non_alias : add_JPoint_and_AFPoint_derive_canonical_non_alias_by_impl_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P2_canonical_non_alias into P2.
  rename P1_canonical_non_alias into P1.
  repeat apply derivable1_orp_elim;
    Intros;
    Exists P1 P2;
    apply sepcon_cancel_end.
  all: try entailer!.
  all: apply derivable1_wand_sepcon_adjoint.
  all: sep_apply
    (store_mixed_add_result_impl_is_canonical
      result_pre P1 P2 ltac:(tauto)).
  all: entailer!.
Qed. 

Lemma proof_of_add_JPoint_and_AFPoint_derive_non_alias_by_impl_non_alias : add_JPoint_and_AFPoint_derive_non_alias_by_impl_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename P2_non_alias into P2.
  rename P1_non_alias into P1.
  Exists P1 P2.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    sep_apply
      (store_mixed_add_result_impl_forget result_pre P1 P2).
    entailer!.
Qed. 

Lemma proof_of_affine_to_jacobian_derive_point_non_alias_by_non_alias : affine_to_jacobian_derive_point_non_alias_by_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_afpoint at 1.
  Intros X Y.
  Exists X Y.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros RX RY RZ.
    unfold store_afpoint, store_jpoint_with_canonical_infinity.
    Exists X Y RX RY RZ.
    pose proof
      (afpoint_to_jpoint_coordinates_represents_canonical
         X Y RX RY RZ P_point_non_alias H H0) as HJ.
    entailer!.
Qed. 
