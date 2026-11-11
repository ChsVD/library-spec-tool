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
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_add_jpoint_and_apoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc_montg Require Import montg_add_jpoint_and_apoint_proof_auto.
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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_and_apoint_lib.
Local Open Scope sac.

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_1_r_eq_a : montg_add_jpoint_and_apoint_return_wit_1_r_eq_a.
Proof.
  unfold montg_add_jpoint_and_apoint_return_wit_1_r_eq_a.
  right; intros.
  Exists (maja_rz AX BX AZ)
    (maja_ry AX AY AZ BX BY)
    (maja_rx AX AY AZ BX BY)
    BY BX.
  unfold store_bn_zero.
  entailer!.
  all: try (unfold maja_rx, maja_ry, maja_rz; apply maja_mod_range).
  all: try (unfold maja_rz; symmetry;
            apply ec_math_refinement.mont_p_mod).
  all: try (unfold maja_ry;
            rewrite ec_math_refinement.mont_p_mod;
            rewrite ec_math_refinement.mont_p_sub;
            reflexivity).
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_2_non_alias : montg_add_jpoint_and_apoint_return_wit_2_non_alias.
Proof.
  unfold montg_add_jpoint_and_apoint_return_wit_2_non_alias.
  right; intros.
  Exists (maja_rz AX BX AZ)
    (maja_ry AX AY AZ BX BY)
    (maja_rx AX AY AZ BX BY)
    AZ AY AX BY BX.
  unfold store_bn_zero.
  entailer!.
  all: try (unfold maja_rx, maja_ry, maja_rz; apply maja_mod_range).
  all: try (unfold maja_rz; symmetry;
            apply ec_math_refinement.mont_p_mod).
  all: try (unfold maja_ry;
            rewrite ec_math_refinement.mont_p_mod;
            rewrite ec_math_refinement.mont_p_sub;
            reflexivity).
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_3_r_eq_a : montg_add_jpoint_and_apoint_return_wit_3_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1.
  unfold store_mont_afpoint, store_mont_afpoint_coords,
    store_afpoint_fields, store_bn_zero.
  Exists BX BY.
  entailer!.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_4_non_alias : montg_add_jpoint_and_apoint_return_wit_4_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hpack_a :
    store_fp &(a_pre # "JPoint" ->ₛ "z") (mont_p AZ) **
    store_fp &(a_pre # "JPoint" ->ₛ "y") (mont_p AY) **
    store_fp &(a_pre # "JPoint" ->ₛ "x") (mont_p AX)
    |-- store_mont_jpoint a_pre P_non_alias).
  {
    unfold store_mont_jpoint, store_mont_jpoint_coords,
      store_jpoint_fields.
    Exists AX AY AZ.
    entailer!.
  }
  assert (Hpack_b :
    store_fp &(b_pre # "AFPoint" ->ₛ "y") (mont_p BY) **
    store_fp &(b_pre # "AFPoint" ->ₛ "x") (mont_p BX)
    |-- store_mont_afpoint b_pre Q_non_alias).
  {
    unfold store_mont_afpoint, store_mont_afpoint_coords,
      store_afpoint_fields.
    Exists BX BY.
    entailer!.
  }
  rewrite <- Hpack_a, <- Hpack_b.
  rewrite PreH1.
  unfold store_bn_zero.
  entailer!.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_5_r_eq_a : montg_add_jpoint_and_apoint_return_wit_5_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst Q_r_eq_a.
  unfold sm2_point_double.
  unfold store_mont_afpoint, store_mont_afpoint_coords,
    store_afpoint_fields, store_bn_zero.
  Exists BX BY.
  entailer!.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_6_non_alias : montg_add_jpoint_and_apoint_return_wit_6_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst Q_non_alias.
  unfold sm2_point_double.
  unfold store_mont_afpoint, store_mont_afpoint_coords,
    store_afpoint_fields, store_bn_zero.
  Exists BX BY.
  entailer!.
  rewrite Z.mul_0_l, Z.add_0_r.
  reflexivity.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_7_r_eq_a : montg_add_jpoint_and_apoint_return_wit_7_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst Q_r_eq_a.
  rewrite sm2_point_add_infinity_right.
  entailer!.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_8_non_alias : montg_add_jpoint_and_apoint_return_wit_8_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst Q_non_alias.
  rewrite sm2_point_add_infinity_right.
  entailer!.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_9_r_eq_a : montg_add_jpoint_and_apoint_return_wit_9_r_eq_a.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst P_r_eq_a.
  rewrite sm2_point_add_infinity_left.
  entailer!.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_return_wit_10_non_alias : montg_add_jpoint_and_apoint_return_wit_10_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst P_non_alias.
  rewrite sm2_point_add_infinity_left.
  entailer!.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_pure : montg_add_jpoint_and_apoint_partial_solve_wit_27_r_eq_a_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists AX AY AZ.
  rewrite <- PreH1.
  entailer!.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_pure : montg_add_jpoint_and_apoint_partial_solve_wit_28_non_alias_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists AX AY AZ.
  rewrite <- PreH1.
  entailer!.
Qed. 

Lemma proof_of_montg_add_jpoint_and_apoint_which_implies_wit_1 : montg_add_jpoint_and_apoint_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed. 
