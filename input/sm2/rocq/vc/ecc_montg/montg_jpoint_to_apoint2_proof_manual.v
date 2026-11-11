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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_jpoint_to_apoint2_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_jpoint_to_apoint2_proof_auto.
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

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_1 : montg_jpoint_to_apoint2_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HZnotone : Z_non_alias <> 1).
  {
    intro HZone.
    subst Z_non_alias.
    apply PreH8.
    unfold MONTG_ONE_Z.
    reflexivity.
  }
  assert (Hp : SM2_P_Z <> 0) by
    (pose proof sm2_p_montgomery_bounds; lia).
  assert (HmontX :
    mont_p (X_non_alias * Zmod (ZI_2 * ZI_2) SM2_P_Z) =
    mont_p (Zmod ((X_non_alias * ZI_2) * ZI_2) SM2_P_Z)).
  {
    unfold mont_p, Montgomery.mont.
    transitivity
      (Zmod
         (Zmod (X_non_alias * Zmod (ZI_2 * ZI_2) SM2_P_Z) SM2_P_Z *
          U256_MOD)
         SM2_P_Z).
    - symmetry. apply Z.mul_mod_idemp_l. exact Hp.
    - rewrite Z.mul_mod_idemp_r by exact Hp.
      replace (X_non_alias * (ZI_2 * ZI_2)) with
        ((X_non_alias * ZI_2) * ZI_2) by ring.
      reflexivity.
  }
  assert (HmontY :
    mont_p (Y_non_alias * Zmod ((ZI_2 * ZI_2) * ZI_2) SM2_P_Z) =
    mont_p (Zmod (((Y_non_alias * ZI_2) * ZI_2) * ZI_2) SM2_P_Z)).
  {
    unfold mont_p, Montgomery.mont.
    transitivity
      (Zmod
         (Zmod
            (Y_non_alias * Zmod ((ZI_2 * ZI_2) * ZI_2) SM2_P_Z)
            SM2_P_Z * U256_MOD)
         SM2_P_Z).
    - symmetry. apply Z.mul_mod_idemp_l. exact Hp.
    - rewrite Z.mul_mod_idemp_r by exact Hp.
      replace (Y_non_alias * ((ZI_2 * ZI_2) * ZI_2)) with
        (((Y_non_alias * ZI_2) * ZI_2) * ZI_2) by ring.
      reflexivity.
  }
  pose proof
    (Z.mod_pos_bound ((X_non_alias * ZI_2) * ZI_2) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))) as HrangeX.
  pose proof
    (Z.mod_pos_bound (((Y_non_alias * ZI_2) * ZI_2) * ZI_2) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))) as HrangeY.
  assert (HpackJP :
    (store_fp (&(a_pre # "JPoint" ->ₛ "x")) (mont_p X_non_alias) **
     store_fp (&(a_pre # "JPoint" ->ₛ "y")) (mont_p Y_non_alias)) **
    store_fp (&(a_pre # "JPoint" ->ₛ "z")) (mont_p Z_non_alias) |--
    store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias).
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
  assert (HpackAF :
    store_fp (&(r_pre # "AFPoint" ->ₛ "x"))
      (mont_p (Zmod ((X_non_alias * ZI_2) * ZI_2) SM2_P_Z)) **
    store_fp (&(r_pre # "AFPoint" ->ₛ "y"))
      (mont_p (Zmod (((Y_non_alias * ZI_2) * ZI_2) * ZI_2) SM2_P_Z)) |--
    store_mont_afpoint_coords r_pre
      (Zmod ((X_non_alias * ZI_2) * ZI_2) SM2_P_Z)
      (Zmod (((Y_non_alias * ZI_2) * ZI_2) * ZI_2) SM2_P_Z)).
  {
    unfold store_mont_afpoint_coords, store_afpoint_fields,
      derivable1, Snaive_C_Rules.andp, Snaive_C_Rules.coq_prop,
      Snaive_C_Rules.sepcon.
    intros m Hm.
    destruct Hm as (m1 & m2 & Hj12 & Hx & Hy).
    split.
    - split; lia.
    - exists m1, m2.
      split; [exact Hj12 |].
      split; assumption.
  }
  Right.
  Exists
    (Zmod (((Y_non_alias * ZI_2) * ZI_2) * ZI_2) SM2_P_Z)
    (Zmod ((X_non_alias * ZI_2) * ZI_2) SM2_P_Z)
    ZI_2.
  split_pure_spatial.
  - rewrite <- HpackJP, <- HpackAF.
    rewrite HmontX, HmontY.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_2 : montg_jpoint_to_apoint2_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (HZone : Z_non_alias = 1).
  {
    apply (mont_p_injective Z_non_alias 1).
    - lia.
    - cbv [SM2_P_Z]. lia.
    - unfold MONTG_ONE_Z in PreH7. exact PreH7.
  }
  subst Z_non_alias.
  assert (HpackJP :
    (store_fp (&(a_pre # "JPoint" ->ₛ "x")) (mont_p X_non_alias) **
     store_fp (&(a_pre # "JPoint" ->ₛ "y")) (mont_p Y_non_alias)) **
    store_fp (&(a_pre # "JPoint" ->ₛ "z")) (mont_p 1) |--
    store_mont_jpoint_coords a_pre X_non_alias Y_non_alias 1).
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
  assert (HpackAF :
    store_fp (&(r_pre # "AFPoint" ->ₛ "x")) (mont_p X_non_alias) **
    store_fp (&(r_pre # "AFPoint" ->ₛ "y")) (mont_p Y_non_alias) |--
    store_mont_afpoint_coords r_pre X_non_alias Y_non_alias).
  {
    unfold store_mont_afpoint_coords, store_afpoint_fields,
      derivable1, Snaive_C_Rules.andp, Snaive_C_Rules.coq_prop,
      Snaive_C_Rules.sepcon.
    intros m Hm.
    destruct Hm as (m1 & m2 & Hj12 & Hx & Hy).
    split.
    - split; lia.
    - exists m1, m2.
      split; [exact Hj12 |].
      split; assumption.
  }
  Left.
  Exists Y_non_alias X_non_alias.
  split_pure_spatial.
  - rewrite <- HpackJP, <- HpackAF.
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_3_split_goal_1 : montg_jpoint_to_apoint2_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbv [SM2_P_Z]; lia).
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_3_split_goal_2 : montg_jpoint_to_apoint2_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbv [SM2_P_Z]; lia).
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_3_split_goal_3 : montg_jpoint_to_apoint2_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(
    unfold mont_p, Montgomery.mont;
    rewrite Z.mul_0_l;
    apply Z.mod_0_l;
    pose proof sm2_p_montgomery_bounds;
    lia).
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_3_split_goal_4 : montg_jpoint_to_apoint2_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(
    unfold mont_p, Montgomery.mont;
    rewrite Z.mul_0_l;
    apply Z.mod_0_l;
    pose proof sm2_p_montgomery_bounds;
    lia).
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_return_wit_3 : montg_jpoint_to_apoint2_return_wit_3.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial. cbv [SM2_P_Z]; lia.
  - try dump_pre_spatial. cbv [SM2_P_Z]; lia.
  - try dump_pre_spatial.
    unfold mont_p, Montgomery.mont.
    rewrite Z.mul_0_l.
    rewrite Z.mod_0_l by (pose proof sm2_p_montgomery_bounds; lia).
    reflexivity.
  - try dump_pre_spatial.
    unfold mont_p, Montgomery.mont.
    rewrite Z.mul_0_l.
    rewrite Z.mod_0_l by (pose proof sm2_p_montgomery_bounds; lia).
    reflexivity.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_2_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  rewrite Z.mul_0_l, Z.add_0_r.
  rewrite <- u32_v_field_address_eq.
  csimpl.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_2_pure : montg_jpoint_to_apoint2_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    rewrite Z.mul_0_l, Z.add_0_r.
    rewrite <- u32_v_field_address_eq.
    csimpl.
    reflexivity.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_3_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  rewrite Z.mul_0_l, Z.add_0_r.
  rewrite <- u32_v_field_address_eq.
  csimpl.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_3_pure : montg_jpoint_to_apoint2_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    rewrite Z.mul_0_l, Z.add_0_r.
    rewrite <- u32_v_field_address_eq.
    csimpl.
    reflexivity.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
  csimpl.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof (mont_p_range Z_non_alias) as HmontZ.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_3 : montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof (mont_p_range Z_non_alias) as HmontZ.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_4_pure : montg_jpoint_to_apoint2_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
    csimpl.
    rewrite Z.mul_0_l, Z.add_0_r.
    reflexivity.
  - try dump_pre_spatial.
    pose proof (mont_p_range Z_non_alias); lia.
  - try dump_pre_spatial.
    pose proof (mont_p_range Z_non_alias); lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  simpl.
  rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  simpl.
  rewrite <- (u32_v_field_address_eq (&(r_pre # "AFPoint" ->ₛ "x"))).
  csimpl.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_3 : montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof (mont_p_range X_non_alias).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_4 : montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof (mont_p_range X_non_alias).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5_pure : montg_jpoint_to_apoint2_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    simpl.
    rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
    lia.
  - try dump_pre_spatial.
    simpl.
    rewrite <- (u32_v_field_address_eq (&(r_pre # "AFPoint" ->ₛ "x"))).
    csimpl.
    lia.
  - try dump_pre_spatial.
    pose proof (mont_p_range X_non_alias); lia.
  - try dump_pre_spatial.
    pose proof (mont_p_range X_non_alias); lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  simpl.
  rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  simpl.
  rewrite <- (u32_v_field_address_eq (&(r_pre # "AFPoint" ->ₛ "y"))).
  csimpl.
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_3 : montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof (mont_p_range Y_non_alias).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_4 : montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof (mont_p_range Y_non_alias).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6_pure : montg_jpoint_to_apoint2_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    simpl.
    rewrite nested_jpoint_u32_v_addr_eq, u32_v_field_address_eq.
    lia.
  - try dump_pre_spatial.
    simpl.
    rewrite <- (u32_v_field_address_eq (&(r_pre # "AFPoint" ->ₛ "y"))).
    csimpl.
    lia.
  - try dump_pre_spatial.
    pose proof (mont_p_range Y_non_alias); lia.
  - try dump_pre_spatial.
    pose proof (mont_p_range Y_non_alias); lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_8_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  rewrite (global_u32_v_addr_eq "T"), u32_v_field_address_eq.
  csimpl.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_8_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  rewrite (global_u32_v_addr_eq "Zinv"), u32_v_field_address_eq.
  csimpl.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_8_pure : montg_jpoint_to_apoint2_partial_solve_wit_8_pure.
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

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold mont_p.
  symmetry.
  apply Montgomery.mont_mod.
  pose proof (proj1 (proj1 sm2_p_montgomery_bounds)).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof
    (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_3 : montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof
    (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_10_pure : montg_jpoint_to_apoint2_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    unfold mont_p.
    symmetry.
    apply Montgomery.mont_mod.
    pose proof (proj1 (proj1 sm2_p_montgomery_bounds)); lia.
  - try dump_pre_spatial.
    pose proof
      (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
         (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
  - try dump_pre_spatial.
    pose proof
      (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
         (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_11_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof
    (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_11_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof
    (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_11_pure : montg_jpoint_to_apoint2_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    pose proof
      (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
         (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
  - try dump_pre_spatial.
    pose proof
      (Z.mod_pos_bound (ZI * ZI) SM2_P_Z
         (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_1 : montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold mont_p.
  rewrite Montgomery.mont_mod by
    (pose proof (proj1 (proj1 sm2_p_montgomery_bounds)); lia).
  unfold Montgomery.mont.
  rewrite <- Z.mul_assoc.
  rewrite <- Z.mul_assoc.
  apply Z.mul_mod_idemp_l.
  pose proof (proj1 (proj1 sm2_p_montgomery_bounds)).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_2 : montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof
    (Z.mod_pos_bound ((ZI * ZI) * ZI) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_3 : montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  pose proof
    (Z.mod_pos_bound ((ZI * ZI) * ZI) SM2_P_Z
       (proj1 (proj1 sm2_p_montgomery_bounds))).
  lia.
Qed.

Lemma proof_of_montg_jpoint_to_apoint2_partial_solve_wit_12_pure : montg_jpoint_to_apoint2_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - try dump_pre_spatial.
    unfold mont_p.
    rewrite Montgomery.mont_mod by
      (pose proof (proj1 (proj1 sm2_p_montgomery_bounds)); lia).
    unfold Montgomery.mont.
    rewrite <- Z.mul_assoc.
    rewrite <- Z.mul_assoc.
    apply Z.mul_mod_idemp_l.
    pose proof (proj1 (proj1 sm2_p_montgomery_bounds)).
    lia.
  - try dump_pre_spatial.
    pose proof
      (Z.mod_pos_bound ((ZI * ZI) * ZI) SM2_P_Z
         (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
  - try dump_pre_spatial.
    pose proof
      (Z.mod_pos_bound ((ZI * ZI) * ZI) SM2_P_Z
         (proj1 (proj1 sm2_p_montgomery_bounds))).
    lia.
Qed. 

Lemma proof_of_montg_jpoint_to_apoint2_derive_point_non_alias_by_non_alias : montg_jpoint_to_apoint2_derive_point_non_alias_by_non_alias.
Proof.
  unfold montg_jpoint_to_apoint2_derive_point_non_alias_by_non_alias.
  intros r_pre a_pre P.
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
    + Split.
      * Intros RY RX retval_2.
        assert (HPinf : P = ECInfinity).
        { apply (proj1 (jpoint_represents_infinity_iff X Y Z P H)).
          exact H1. }
        assert (Haff : afpoint_represents RX RY P).
        { subst P RX RY.
          unfold ECInfinity.
          cbn [afpoint_represents afpoint_infinity].
          unfold afpoint_infinity.
          tauto. }
        assert (Haf_store :
          store_mont_afpoint_coords r_pre RX RY |--
          store_mont_afpoint r_pre P).
        { unfold store_mont_afpoint. Exists RX RY. entailer!. }
        sep_apply_l_atomic Hpoint.
        sep_apply_l_atomic Haf_store.
        Exists 1.
        entailer!.
      * Intros RY RX retval_2.
        assert (Hbounds :
          0 <= X < SM2_P_Z /\
          0 <= Y < SM2_P_Z /\
          0 <= Z < SM2_P_Z).
        { unfold jpoint_represents in H. tauto. }
        assert (Hconvert :
          jpoint_to_afpoint_coordinates X Y Z RX RY).
        { subst Z RX RY.
          unfold jpoint_to_afpoint_coordinates.
          right.
          split; [lia |].
          exists 1.
          repeat split; try lia.
          - rewrite Z.pow_2_r.
            replace (X * (1 * 1)) with X by ring.
            rewrite Z.mod_small; [reflexivity | tauto].
          - replace (Y * 1 ^ 3) with Y by ring.
            rewrite Z.mod_small; [reflexivity | tauto]. }
        pose proof
          (jpoint_to_afpoint_coordinates_represents
            X Y Z RX RY P H Hconvert) as Haff.
        assert (Haf_store :
          store_mont_afpoint_coords r_pre RX RY |--
          store_mont_afpoint r_pre P).
        { unfold store_mont_afpoint. Exists RX RY. entailer!. }
        sep_apply_l_atomic Hpoint.
        sep_apply_l_atomic Haf_store.
        Exists 1.
        entailer!.
    + Intros RY RX ZI retval_2.
      assert (Hconvert :
        jpoint_to_afpoint_coordinates X Y Z RX RY).
      { unfold jpoint_to_afpoint_coordinates.
        right.
        split; [exact H1 |].
        exists ZI.
        repeat split; try assumption.
        - rewrite H6. f_equal. ring.
        - rewrite H7. f_equal. ring. }
      pose proof
        (jpoint_to_afpoint_coordinates_represents
          X Y Z RX RY P H Hconvert) as Haff.
      assert (Haf_store :
        store_mont_afpoint_coords r_pre RX RY |--
        store_mont_afpoint r_pre P).
      { unfold store_mont_afpoint. Exists RX RY. entailer!. }
      sep_apply_l_atomic Hpoint.
      sep_apply_l_atomic Haf_store.
      Exists 1.
      entailer!.
Qed. 
