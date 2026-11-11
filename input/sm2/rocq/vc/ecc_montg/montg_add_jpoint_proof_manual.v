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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_add_jpoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_add_jpoint_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_lib.
Local Open Scope sac.

Lemma proof_of_montg_add_jpoint_return_wit_1_non_alias : montg_add_jpoint_return_wit_1_non_alias.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields.
  Exists AX AY AZ BX BY BZ
    (aj_rx AX AY AZ BX BY BZ)
    (aj_ry AX AY AZ BX BY BZ)
    (aj_rz AX AZ BX BZ).
  assert (HY :
    fp_div2 (mont_p (aj_y_num AX AY AZ BX BY BZ)) =
    mont_p (aj_ry AX AY AZ BX BY BZ)).
  {
    rewrite ec_math_refinement.fp_div2_mont.
    apply montg_add_ry_mont.
  }
  assert (HZ :
    mont_p (aj_zbase AZ BZ * aj_h AX AZ BX BZ) =
    mont_p (aj_rz AX AZ BX BZ)).
  {
    unfold aj_rz.
    symmetry; apply ec_math_refinement.mont_p_mod.
  }
  rewrite HY, HZ.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (unfold aj_rx, aj_ry, aj_rz; apply aj_mod_range).
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_2_r_eq_a : montg_add_jpoint_return_wit_2_r_eq_a.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields.
  Exists (aj_rx AX AY AZ BX BY BZ)
    (aj_ry AX AY AZ BX BY BZ)
    (aj_rz AX AZ BX BZ) BX BY BZ.
  assert (HY :
    fp_div2 (mont_p (aj_y_num AX AY AZ BX BY BZ)) =
    mont_p (aj_ry AX AY AZ BX BY BZ)).
  {
    rewrite ec_math_refinement.fp_div2_mont.
    apply montg_add_ry_mont.
  }
  assert (HZ :
    mont_p (aj_zbase AZ BZ * aj_h AX AZ BX BZ) =
    mont_p (aj_rz AX AZ BX BZ)).
  {
    unfold aj_rz.
    symmetry; apply ec_math_refinement.mont_p_mod.
  }
  rewrite HY, HZ.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (unfold aj_rx, aj_ry, aj_rz; apply aj_mod_range).
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_3_r_eq_b : montg_add_jpoint_return_wit_3_r_eq_b.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields.
  Exists AX AY AZ
    (aj_rx AX AY AZ BX BY BZ)
    (aj_ry AX AY AZ BX BY BZ)
    (aj_rz AX AZ BX BZ).
  assert (HY :
    fp_div2 (mont_p (aj_y_num AX AY AZ BX BY BZ)) =
    mont_p (aj_ry AX AY AZ BX BY BZ)).
  {
    rewrite ec_math_refinement.fp_div2_mont.
    apply montg_add_ry_mont.
  }
  assert (HZ :
    mont_p (aj_zbase AZ BZ * aj_h AX AZ BX BZ) =
    mont_p (aj_rz AX AZ BX BZ)).
  {
    unfold aj_rz.
    symmetry; apply ec_math_refinement.mont_p_mod.
  }
  rewrite HY, HZ.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (unfold aj_rx, aj_ry, aj_rz; apply aj_mod_range).
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_4_r_eq_b : montg_add_jpoint_return_wit_4_r_eq_b.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields.
  Exists AX AY AZ
    (aj_rx AX AY AZ BX BY BZ)
    (aj_ry AX AY AZ BX BY BZ)
    (aj_rz AX AZ BX BZ).
  assert (HY :
    fp_div2 (mont_p (aj_y_num AX AY AZ BX BY BZ)) =
    mont_p (aj_ry AX AY AZ BX BY BZ)).
  {
    rewrite ec_math_refinement.fp_div2_mont.
    apply montg_add_ry_mont.
  }
  assert (HZ :
    mont_p (aj_zbase AZ BZ * aj_h AX AZ BX BZ) =
    mont_p (aj_rz AX AZ BX BZ)).
  {
    unfold aj_rz.
    symmetry; apply ec_math_refinement.mont_p_mod.
  }
  rewrite HY, HZ.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (unfold aj_rx, aj_ry, aj_rz; apply aj_mod_range).
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_5_r_eq_a : montg_add_jpoint_return_wit_5_r_eq_a.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields.
  Exists (aj_rx AX AY AZ BX BY BZ)
    (aj_ry AX AY AZ BX BY BZ)
    (aj_rz AX AZ BX BZ) BX BY BZ.
  assert (HY :
    fp_div2 (mont_p (aj_y_num AX AY AZ BX BY BZ)) =
    mont_p (aj_ry AX AY AZ BX BY BZ)).
  {
    rewrite ec_math_refinement.fp_div2_mont.
    apply montg_add_ry_mont.
  }
  assert (HZ :
    mont_p (aj_zbase AZ BZ * aj_h AX AZ BX BZ) =
    mont_p (aj_rz AX AZ BX BZ)).
  {
    unfold aj_rz.
    symmetry; apply ec_math_refinement.mont_p_mod.
  }
  rewrite HY, HZ.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (unfold aj_rx, aj_ry, aj_rz; apply aj_mod_range).
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_6_non_alias : montg_add_jpoint_return_wit_6_non_alias.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields.
  Exists AX AY AZ BX BY BZ
    (aj_rx AX AY AZ BX BY BZ)
    (aj_ry AX AY AZ BX BY BZ)
    (aj_rz AX AZ BX BZ).
  assert (HY :
    fp_div2 (mont_p (aj_y_num AX AY AZ BX BY BZ)) =
    mont_p (aj_ry AX AY AZ BX BY BZ)).
  {
    rewrite ec_math_refinement.fp_div2_mont.
    apply montg_add_ry_mont.
  }
  assert (HZ :
    mont_p (aj_zbase AZ BZ * aj_h AX AZ BX BZ) =
    mont_p (aj_rz AX AZ BX BZ)).
  {
    unfold aj_rz.
    symmetry; apply ec_math_refinement.mont_p_mod.
  }
  rewrite HY, HZ.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (unfold aj_rx, aj_ry, aj_rz; apply aj_mod_range).
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_7_r_eq_b : montg_add_jpoint_return_wit_7_r_eq_b.
Proof.
  unfold montg_add_jpoint_return_wit_7_r_eq_b.
  left; intros.
  subst b_pre retval.
  rewrite <- PreH1.
  unfold sm2_point_double.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_return_wit_8_r_eq_a : montg_add_jpoint_return_wit_8_r_eq_a.
Proof.
  LLM_pre_process ltac:(reflexivity).
  assert (Hpack :
    store_fp &(b_pre # "JPoint" ->ₛ "z") (mont_p BZ) **
    (store_fp &(b_pre # "JPoint" ->ₛ "y") (mont_p BY) **
     store_fp &(b_pre # "JPoint" ->ₛ "x") (mont_p BX))
    |-- store_mont_jpoint b_pre Q_r_eq_a).
  {
    unfold store_mont_jpoint, store_mont_jpoint_coords,
      store_jpoint_fields.
    Exists BX BY BZ.
    split_pure_spatial.
    - sepcon_assoc_change.
      cancel.
    - split_pures;
      dump_pre_spatial;
      try lia;
      assumption.
  }
  replace (sm2_point_add P_r_eq_a Q_r_eq_a)
    with (sm2_point_add P_r_eq_a P_r_eq_a) by now rewrite PreH2.
  unfold sm2_point_double.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
    exact Hpack.
  - split_pures;
    dump_pre_spatial;
    try reflexivity;
    assumption.
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_9_non_alias : montg_add_jpoint_return_wit_9_non_alias.
Proof.
  LLM_pre_process ltac:(reflexivity).
  assert (Hpack :
    store_fp &(b_pre # "JPoint" ->ₛ "z") (mont_p BZ) **
    (store_fp &(b_pre # "JPoint" ->ₛ "y") (mont_p BY) **
     store_fp &(b_pre # "JPoint" ->ₛ "x") (mont_p BX))
    |-- store_mont_jpoint b_pre Q_non_alias).
  {
    unfold store_mont_jpoint, store_mont_jpoint_coords,
      store_jpoint_fields.
    Exists BX BY BZ.
    split_pure_spatial.
    - sepcon_assoc_change.
      cancel.
    - split_pures;
      dump_pre_spatial;
      try lia;
      assumption.
  }
  replace (sm2_point_add P_non_alias Q_non_alias)
    with (sm2_point_add P_non_alias P_non_alias) by now rewrite PreH1.
  unfold sm2_point_double.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
    exact Hpack.
  - split_pures;
    dump_pre_spatial;
    try reflexivity;
    assumption.
Qed. 

Lemma proof_of_montg_add_jpoint_return_wit_10_r_eq_b : montg_add_jpoint_return_wit_10_r_eq_b.
Proof.
  unfold montg_add_jpoint_return_wit_10_r_eq_b.
  left; intros.
  subst Q_r_eq_b b_pre retval.
  rewrite sm2_point_add_infinity_right.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_return_wit_11_r_eq_a : montg_add_jpoint_return_wit_11_r_eq_a.
Proof.
  unfold montg_add_jpoint_return_wit_11_r_eq_a.
  left; intros.
  subst Q_r_eq_a a_pre retval.
  rewrite sm2_point_add_infinity_right.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_return_wit_12_non_alias : montg_add_jpoint_return_wit_12_non_alias.
Proof.
  unfold montg_add_jpoint_return_wit_12_non_alias.
  left; intros.
  subst Q_non_alias retval.
  rewrite sm2_point_add_infinity_right.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_return_wit_13_r_eq_b : montg_add_jpoint_return_wit_13_r_eq_b.
Proof.
  unfold montg_add_jpoint_return_wit_13_r_eq_b.
  left; intros.
  subst P_r_eq_b b_pre retval.
  rewrite sm2_point_add_infinity_left.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_return_wit_14_r_eq_a : montg_add_jpoint_return_wit_14_r_eq_a.
Proof.
  unfold montg_add_jpoint_return_wit_14_r_eq_a.
  left; intros.
  subst P_r_eq_a a_pre retval.
  rewrite sm2_point_add_infinity_left.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_return_wit_15_non_alias : montg_add_jpoint_return_wit_15_non_alias.
Proof.
  unfold montg_add_jpoint_return_wit_15_non_alias.
  left; intros.
  subst P_non_alias retval.
  rewrite sm2_point_add_infinity_left.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures;
    dump_pre_spatial;
    reflexivity.
Qed.

Lemma proof_of_montg_add_jpoint_partial_solve_wit_46_r_eq_b_pure : montg_add_jpoint_partial_solve_wit_46_r_eq_b_pure.
Proof.
  LLM_pre_process ltac:(reflexivity).
  Exists AX AY AZ.
  rewrite <- PreH1.
  split_pures;
  dump_pre_spatial;
  try reflexivity;
  assumption.
Qed. 

Lemma proof_of_montg_add_jpoint_partial_solve_wit_47_r_eq_a_pure : montg_add_jpoint_partial_solve_wit_47_r_eq_a_pure.
Proof.
  LLM_pre_process ltac:(reflexivity).
  Exists AX AY AZ.
  rewrite <- PreH1.
  split_pures;
  dump_pre_spatial;
  try reflexivity;
  assumption.
Qed. 

Lemma proof_of_montg_add_jpoint_partial_solve_wit_48_non_alias_pure : montg_add_jpoint_partial_solve_wit_48_non_alias_pure.
Proof.
  LLM_pre_process ltac:(reflexivity).
  Exists AX AY AZ.
  rewrite <- PreH1.
  split_pures;
  dump_pre_spatial;
  try reflexivity;
  assumption.
Qed. 
