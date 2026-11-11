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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_mod_p_def.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_mod_p_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import mul_mod_p_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_mul_mod_p_entail_wit_4_x_eq_y : mul_mod_p_entail_wit_4_x_eq_y.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst y_pre.
  unfold store_fp, store_mod, UndefStructPredu32.
  entailer!.
Qed. 

Lemma proof_of_mul_mod_p_entail_wit_5_r_eq_x_split_goal_spatial : mul_mod_p_entail_wit_5_r_eq_x_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mul_mod_p_entail_wit_5_r_eq_x : mul_mod_p_entail_wit_5_r_eq_x.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  entailer!.
  assert (Hundef : forall p x,
    store_u256 p x |-- UndefStructPredu32 p).
  {
    intros p x.
    unfold store_u256, UndefStructPredu32.
    apply store_u256_limbs_to_undef_full.
  }
  sep_apply (Hundef x_pre 1).
  entailer!.
Qed. 

Lemma proof_of_mul_mod_p_entail_wit_6_r_eq_y : mul_mod_p_entail_wit_6_r_eq_y.
Proof.
  unfold mul_mod_p_entail_wit_6_r_eq_y.
  right.
  intros.
  unfold store_fp, store_mod, store_u256, store_u256_limbs.
  Intros x0 x1 x2 x3.
  destruct H0 as [Hx0 [Hx1 [Hx2 [Hx3 Hvalue]]]].
  subst result_pre.
  Exists (x0 :: x1 :: x2 :: x3 :: nil).
  unfold StructPredu32, UInt64Array.full, store_array.
  simpl u32_v.
  cbn [store_array_rec].
  rewrite u64_list_value_four.
  entailer!.
  unfold u64_list_bounded.
  repeat rewrite limb_list_bounded_cons_iff.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  unfold limb_list_bounded.
  intros i Hi.
  rewrite Zlength_nil in Hi.
  lia.
Qed. 

Lemma proof_of_mul_mod_p_entail_wit_14_r_eq_x : mul_mod_p_entail_wit_14_r_eq_x.
Proof.
  unfold mul_mod_p_entail_wit_14_r_eq_x.
  right; intros.
  subst result_pre.
  Exists (x0 :: x1 :: x2 :: x3 :: nil).
  unfold StructPredu32, UInt64Array.full, store_array.
  simpl u32_v.
  cbn [store_array_rec].
  rewrite u64_list_value_four.
  entailer!.
  - replace (0 + 1) with 1 by lia.
    replace (1 + 1) with 2 by lia.
    replace (2 + 1) with 3 by lia.
    cancel.
  - unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    unfold limb_list_bounded.
    intros i Hi.
    rewrite Zlength_nil in Hi.
    lia.
Qed. 

Lemma proof_of_mul_mod_p_entail_wit_15_r_eq_y_split_goal_spatial : mul_mod_p_entail_wit_15_r_eq_y_split_goal_spatial.
Proof. Abort.

Lemma proof_of_mul_mod_p_entail_wit_15_r_eq_y : mul_mod_p_entail_wit_15_r_eq_y.
Proof.
  unfold mul_mod_p_entail_wit_15_r_eq_y.
  right; intros.
  subst result_pre.
  apply store_u256_to_undef.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_1 : mul_mod_p_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_2 : mul_mod_p_return_wit_1_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_r, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_3 : mul_mod_p_return_wit_1_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_r, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_4 : mul_mod_p_return_wit_1_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four, Z.mul_1_r, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_1_non_alias : mul_mod_p_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_1.
  - Goal_apply proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_2.
  - Goal_apply proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_3.
  - Goal_apply proof_of_mul_mod_p_return_wit_1_non_alias_split_goal_4.
Qed.

Lemma proof_of_mul_mod_p_return_wit_2_r_eq_x : mul_mod_p_return_wit_2_r_eq_x.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst result_pre.
  unfold store_fp, store_mod.
  Intros.
  unfold StructPredu32.
  sep_apply (uint64_full4_to_store_u256_limbs
    (&(x_pre # "u32" ->ₛ "v")) limbs).
  unfold store_u256.
  rewrite PreH14, Z.mul_1_r.
  rewrite Zmod_small by lia.
  entailer!.
  assert (Hvalue : u256_of_limbs x0 x1 x2 x3 = 1) by lia.
  assert (Hy :
    ((&(y_pre # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) # UInt64 |-> x3) **
    ((&(y_pre # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
    ((&(y_pre # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
    ((&(y_pre # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) # UInt64 |-> x0)
    |-- store_u256_limbs (&(y_pre # "u32" ->ₛ "v"))
          (u256_of_limbs x0 x1 x2 x3)).
  {
    unfold store_u256_limbs.
    Exists x0 x1 x2 x3.
    entailer!.
  }
  sep_apply Hy.
  rewrite PreH19, Hvalue.
  entailer!.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_1 : mul_mod_p_return_wit_3_r_eq_y_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_2 : mul_mod_p_return_wit_3_r_eq_y_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_r, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_3 : mul_mod_p_return_wit_3_r_eq_y_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_r, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_4 : mul_mod_p_return_wit_3_r_eq_y_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four, Z.mul_1_r, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_3_r_eq_y : mul_mod_p_return_wit_3_r_eq_y.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_1.
  - Goal_apply proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_2.
  - Goal_apply proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_3.
  - Goal_apply proof_of_mul_mod_p_return_wit_3_r_eq_y_split_goal_4.
Qed.

Lemma proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_1 : mul_mod_p_return_wit_4_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_2 : mul_mod_p_return_wit_4_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_3 : mul_mod_p_return_wit_4_non_alias_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_4 : mul_mod_p_return_wit_4_non_alias_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four, Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_4_non_alias : mul_mod_p_return_wit_4_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_1.
  - Goal_apply proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_2.
  - Goal_apply proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_3.
  - Goal_apply proof_of_mul_mod_p_return_wit_4_non_alias_split_goal_4.
Qed.

Lemma proof_of_mul_mod_p_return_wit_5_x_eq_y : mul_mod_p_return_wit_5_x_eq_y.
Proof.
  unfold mul_mod_p_return_wit_5_x_eq_y.
  right; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  entailer!.
  Exists x3 x2 x1 x0.
  rewrite u64_list_value_four.
  rewrite PreH13.
  rewrite Zmod_small by (cbv [SM2_P_Z]; lia).
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer!.
  replace (0 + 1) with 1 by lia.
  replace (1 + 1) with 2 by lia.
  replace (2 + 1) with 3 by lia.
  cancel.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_1 : mul_mod_p_return_wit_6_r_eq_x_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_2 : mul_mod_p_return_wit_6_r_eq_x_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_3 : mul_mod_p_return_wit_6_r_eq_x_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four, Z.mul_1_l, Zmod_small by lia.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_4 : mul_mod_p_return_wit_6_r_eq_x_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite u64_list_value_four.
  lia.
Qed.

Lemma proof_of_mul_mod_p_return_wit_6_r_eq_x : mul_mod_p_return_wit_6_r_eq_x.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_1.
  - Goal_apply proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_2.
  - Goal_apply proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_3.
  - Goal_apply proof_of_mul_mod_p_return_wit_6_r_eq_x_split_goal_4.
Qed.

Lemma proof_of_mul_mod_p_return_wit_7_r_eq_y : mul_mod_p_return_wit_7_r_eq_y.
Proof.
  unfold mul_mod_p_return_wit_7_r_eq_y.
  right; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  entailer!.
  unfold StructPredu32.
  sep_apply (uint64_full4_to_store_u256_limbs
    (&(y_pre # "u32" ->ₛ "v")) limbs).
  unfold store_u256_limbs.
  Intros x0_2 x1_2 x2_2 x3_2.
  Exists x3_2 x2_2 x1_2 x0_2.
  rewrite Z.mul_1_l.
  rewrite Zmod_small by lia.
  entailer!.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_8_r_eq_y : mul_mod_p_return_wit_8_r_eq_y.
Proof.
  unfold mul_mod_p_return_wit_8_r_eq_y.
  right; intros.
  assert (Hres :
    Zout = Zmod (X_r_eq_y * Y_r_eq_y) SM2_P_Z).
  {
    symmetry.
    apply (canonical_residue_from_decomposition
      SM2_P_Z (X_r_eq_y * Y_r_eq_y) Zout K).
    - cbv [SM2_P_Z]. lia.
    - exact (conj PreH4 PreH5).
    - exact PreH6.
  }
  unfold store_u256_limbs.
  Intros sx0 sx1 sx2 sx3.
  Exists sx3 sx2 sx1 sx0.
  csimpl.
  entailer!.
  rewrite !sizeof_uint64.
  cbn.
  repeat rewrite Z.add_0_r.
  cancel.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_9_r_eq_x : mul_mod_p_return_wit_9_r_eq_x.
Proof.
  unfold mul_mod_p_return_wit_9_r_eq_x.
  right; intros.
  assert (Hres :
    Zout = Zmod (X_r_eq_x * Y_r_eq_x) SM2_P_Z).
  {
    symmetry.
    apply (canonical_residue_from_decomposition
      SM2_P_Z (X_r_eq_x * Y_r_eq_x) Zout K).
    - cbv [SM2_P_Z]. lia.
    - exact (conj PreH4 PreH5).
    - exact PreH6.
  }
  unfold store_u256_limbs.
  Intros sy0 sy1 sy2 sy3.
  Exists sy3 sy2 sy1 sy0.
  csimpl.
  entailer!.
  rewrite !sizeof_uint64.
  cbn.
  repeat rewrite Z.add_0_r.
  cancel.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_10_x_eq_y : mul_mod_p_return_wit_10_x_eq_y.
Proof.
  unfold mul_mod_p_return_wit_10_x_eq_y.
  right; intros.
  assert (Hres :
    Zout = Zmod (X_x_eq_y * X_x_eq_y) SM2_P_Z).
  {
    symmetry.
    apply (canonical_residue_from_decomposition
      SM2_P_Z (X_x_eq_y * X_x_eq_y) Zout K).
    - cbv [SM2_P_Z]. lia.
    - exact (conj PreH4 PreH5).
    - exact PreH6.
  }
  unfold store_u256_limbs.
  Intros sx0 sx1 sx2 sx3.
  Exists sx3 sx2 sx1 sx0.
  csimpl.
  entailer!.
  rewrite !sizeof_uint64.
  cbn.
  repeat rewrite Z.add_0_r.
  cancel.
Qed. 

Lemma proof_of_mul_mod_p_return_wit_11_non_alias : mul_mod_p_return_wit_11_non_alias.
Proof.
  unfold mul_mod_p_return_wit_11_non_alias.
  right; intros.
  assert (Hres :
    Zout = Zmod (X_non_alias * Y_non_alias) SM2_P_Z).
  {
    symmetry.
    apply (canonical_residue_from_decomposition
      SM2_P_Z (X_non_alias * Y_non_alias) Zout K).
    - cbv [SM2_P_Z]. lia.
    - exact (conj PreH4 PreH5).
    - exact PreH6.
  }
  unfold store_u256_limbs.
  Intros sx0 sx1 sx2 sx3 sy0 sy1 sy2 sy3.
  Exists sy3 sy2 sy1 sy0 sx3 sx2 sx1 sx0.
  csimpl.
  entailer!.
  rewrite !sizeof_uint64.
  cbn.
  repeat rewrite Z.add_0_r.
  cancel.
Qed. 
