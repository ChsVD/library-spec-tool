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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_jpoint_to_apoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_jpoint_to_apoint_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_montg_jpoint_to_apoint_return_wit_1 : montg_jpoint_to_apoint_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HpackJP :
    (store_fp (&(a_pre # "JPoint" ->ₛ "x")) (mont_p X_x_only) **
     store_fp (&(a_pre # "JPoint" ->ₛ "y")) (mont_p Y_x_only)) **
    store_fp (&(a_pre # "JPoint" ->ₛ "z")) (mont_p Z_x_only) |--
    store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only).
  {
    unfold store_mont_jpoint_coords, store_jpoint_fields,
      derivable1, Snaive_C_Rules.andp, Snaive_C_Rules.coq_prop,
      Snaive_C_Rules.sepcon.
    intros m Hm.
    destruct Hm as (m12 & m3 & Hj123 & Hm12 & Hz).
    destruct Hm12 as (m1 & m2 & Hj12 & Hx & Hy).
    split.
    - split.
      + split; lia.
      + lia.
    - exists m12, m3.
      split; [exact Hj123 |].
      split.
      + exists m1, m2.
        split; [exact Hj12 |].
        split; assumption.
      + exact Hz.
  }
  Exists (Zmod (X_x_only * ZI_2 * ZI_2) SM2_P_Z) ZI_2.
  split_pure_spatial.
  - rewrite <- HpackJP.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_return_wit_2 : montg_jpoint_to_apoint_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HZone : Z_x_only = 1).
  {
    apply (mont_p_injective Z_x_only 1).
    - lia.
    - cbv [SM2_P_Z]. lia.
    - unfold MONTG_ONE_Z in PreH3.
      exact PreH3.
  }
  subst Z_x_only.
  assert (HpackJP :
    (store_fp (&(a_pre # "JPoint" ->ₛ "x")) (mont_p X_x_only) **
     store_fp (&(a_pre # "JPoint" ->ₛ "y")) (mont_p Y_x_only)) **
    store_fp (&(a_pre # "JPoint" ->ₛ "z")) (mont_p 1) |--
    store_mont_jpoint_coords a_pre X_x_only Y_x_only 1).
  {
    unfold store_mont_jpoint_coords, store_jpoint_fields,
      derivable1, Snaive_C_Rules.andp, Snaive_C_Rules.coq_prop,
      Snaive_C_Rules.sepcon.
    intros m Hm.
    destruct Hm as (m12 & m3 & Hj123 & Hm12 & Hz).
    destruct Hm12 as (m1 & m2 & Hj12 & Hx & Hy).
    split.
    - split.
      + split; lia.
      + lia.
    - exists m12, m3.
      split; [exact Hj123 |].
      split.
      + exists m1, m2.
        split; [exact Hj12 |].
        split; assumption.
      + exact Hz.
  }
  assert (HmodX :
    Zmod (X_x_only * 1 * 1) SM2_P_Z = X_x_only).
  {
    replace (X_x_only * 1 * 1) with X_x_only by ring.
    apply Z.mod_small.
    lia.
  }
  assert (HmodOne : Zmod (1 * 1) SM2_P_Z = 1).
  {
    replace (1 * 1) with 1 by ring.
    apply Z.mod_small.
    cbv [SM2_P_Z]. lia.
  }
  Exists X_x_only 1.
  split_pure_spatial.
  - rewrite <- HpackJP.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_1 : montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
  csimpl.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_2 : montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mont_p, Montgomery.mont.
  pose proof (Z.mod_pos_bound
    (Z_x_only * U256_MOD) SM2_P_Z ltac:(cbv [SM2_P_Z]; lia)).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_3 : montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mont_p, Montgomery.mont.
  pose proof (Z.mod_pos_bound
    (Z_x_only * U256_MOD) SM2_P_Z ltac:(cbv [SM2_P_Z]; lia)).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_3_pure : montg_jpoint_to_apoint_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
    csimpl.
    rewrite Z.mul_0_l, Z.add_0_r.
    reflexivity.
  - try dump_pre_spatial.
    unfold mont_p, Montgomery.mont.
    pose proof (Z.mod_pos_bound
      (Z_x_only * U256_MOD) SM2_P_Z ltac:(cbv [SM2_P_Z]; lia)).
    lia.
  - try dump_pre_spatial.
    unfold mont_p, Montgomery.mont.
    pose proof (Z.mod_pos_bound
      (Z_x_only * U256_MOD) SM2_P_Z ltac:(cbv [SM2_P_Z]; lia)).
    lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_6_pure_split_goal_1 : montg_jpoint_to_apoint_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (global_u32_v_addr_eq "T"), u32_v_field_address_eq.
  csimpl.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_6_pure_split_goal_2 : montg_jpoint_to_apoint_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite (global_u32_v_addr_eq "Zinv"), u32_v_field_address_eq.
  csimpl.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_6_pure : montg_jpoint_to_apoint_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    rewrite (global_u32_v_addr_eq "T"), u32_v_field_address_eq.
    csimpl.
    rewrite Z.mul_0_l, Z.add_0_r.
    reflexivity.
  - try dump_pre_spatial.
    rewrite (global_u32_v_addr_eq "Zinv"), u32_v_field_address_eq.
    csimpl.
    rewrite Z.mul_0_l, Z.add_0_r.
    reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_1 : montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mont_p, Montgomery.mont.
  rewrite Z.mul_mod_idemp_l by
    (pose proof sm2_p_montgomery_bounds; lia).
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_2 : montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
    (proj1 (proj1 sm2_p_montgomery_bounds))) as Hmod.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_3 : montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
    (proj1 (proj1 sm2_p_montgomery_bounds))) as Hmod.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_8_pure : montg_jpoint_to_apoint_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    unfold mont_p, Montgomery.mont.
    rewrite Z.mul_mod_idemp_l by
      (pose proof sm2_p_montgomery_bounds; lia).
    reflexivity.
  - try dump_pre_spatial.
    pose proof (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
      (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
  - try dump_pre_spatial.
    pose proof (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
      (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_1 : montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold mont_p, Montgomery.mont.
  assert (Hp : SM2_P_Z <> 0) by
    (pose proof sm2_p_montgomery_bounds; lia).
  transitivity
    (Zmod
       (Zmod (X_x_only * Zmod (ZI * ZI) SM2_P_Z) SM2_P_Z * U256_MOD)
       SM2_P_Z).
  - symmetry. apply Z.mul_mod_idemp_l. exact Hp.
  - rewrite Z.mul_mod_idemp_r by exact Hp.
    replace (X_x_only * (ZI * ZI)) with
      ((X_x_only * ZI) * ZI) by ring.
    reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_2 : montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound ((X_x_only * ZI) * ZI) SM2_P_Z
    (proj1 (proj1 sm2_p_montgomery_bounds))) as Hmod.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_3 : montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound ((X_x_only * ZI) * ZI) SM2_P_Z
    (proj1 (proj1 sm2_p_montgomery_bounds))) as Hmod.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_partial_solve_wit_9_pure : montg_jpoint_to_apoint_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    unfold mont_p, Montgomery.mont.
    assert (Hp : SM2_P_Z <> 0) by
      (pose proof sm2_p_montgomery_bounds; lia).
    transitivity
      (Zmod
         (Zmod (X_x_only * Zmod (ZI * ZI) SM2_P_Z) SM2_P_Z * U256_MOD)
         SM2_P_Z).
    + symmetry. apply Z.mul_mod_idemp_l. exact Hp.
    + rewrite Z.mul_mod_idemp_r by exact Hp.
      replace (X_x_only * (ZI * ZI)) with
        ((X_x_only * ZI) * ZI) by ring.
      reflexivity.
  - try dump_pre_spatial.
    pose proof (Z.mod_pos_bound ((X_x_only * ZI) * ZI) SM2_P_Z
      (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
  - try dump_pre_spatial.
    pose proof (Z.mod_pos_bound ((X_x_only * ZI) * ZI) SM2_P_Z
      (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint_derive_point_x_only_by_x_only : montg_jpoint_to_apoint_derive_point_x_only_by_x_only.
Proof.
  unfold montg_jpoint_to_apoint_derive_point_x_only_by_x_only.
  intros ry_pre rx_pre a_pre P.
  unfold store_mont_jpoint at 1.
  Intros X Y Z.
  Exists X Y Z.
  apply sepcon_cancel_end.
  - entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    assert (Hpoint :
      store_mont_jpoint_coords a_pre X Y Z |--
      store_mont_jpoint a_pre P).
    { unfold store_mont_jpoint. Exists X Y Z. entailer!. }
    Split.
    + Intros retval_2 RX_2.
      pose proof
        (jpoint_x_coordinate_represents
          X Y Z retval_2 P H1 (or_introl (conj H4 H5)))
        as [RY Haff].
      sep_apply_l_atomic Hpoint.
      Exists retval_2 RY 1.
      entailer!.
    + Intros retval_2 ZI RX_2.
      assert (Hobs :
        (Z = 0 /\ retval_2 = 0) \/
        (Z <> 0 /\ exists z_inverse,
          0 <= z_inverse < SM2_P_Z /\
          Zmod (Z * z_inverse) SM2_P_Z = 1 /\
          retval_2 = Zmod (X * z_inverse * z_inverse) SM2_P_Z)).
      { right. split; [exact H4 |].
        exists ZI. repeat split; assumption. }
      pose proof
        (jpoint_x_coordinate_represents X Y Z retval_2 P H1 Hobs)
        as [RY Haff].
      sep_apply_l_atomic Hpoint.
      Exists retval_2 RY 1.
      entailer!.
Qed.
