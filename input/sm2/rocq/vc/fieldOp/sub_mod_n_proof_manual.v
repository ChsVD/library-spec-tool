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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import sub_mod_n_goal.
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import sub_mod_n_proof_auto.
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

Lemma proof_of_sub_mod_n_return_wit_1_r_eq_b_split_goal_1 : sub_mod_n_return_wit_1_r_eq_b_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_1_r_eq_b_split_goal_2 : sub_mod_n_return_wit_1_r_eq_b_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_1_r_eq_b_split_goal_3 : sub_mod_n_return_wit_1_r_eq_b_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_1_r_eq_b : sub_mod_n_return_wit_1_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || entailer!).
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  rewrite (unsigned_lnot_u64 x0_2 ltac:(lia)) in PreH41.
  rewrite (unsigned_lnot_u64 x1_2 ltac:(lia)) in PreH36.
  rewrite (unsigned_lnot_u64 x2_2 ltac:(lia)) in PreH31.
  rewrite (unsigned_lnot_u64 x3_2 ltac:(lia)) in PreH26.
  pose proof (addcarry4_weighted_bridge U64_MOD
    x0 x1 x2 x3
    (U64_MOD - x0_2) (U64_MOD - 1 - x1_2)
    (U64_MOD - 1 - x2_2) (U64_MOD - 1 - x3_2)
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    ltac:(lia) PreH36 PreH31 PreH26) as Hweighted.
  assert (Hdiff : A_r_eq_b - B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + (retval_4 - 1) * U256_MOD).
  {
    rewrite PreH51, PreH42.
    unfold u256_of_limbs.
    rewrite U256_MOD_as_U64_POW_4.
    unfold U64_POW.
    apply (proj1 (Z.add_cancel_r _ _ (U64_MOD ^ 4))).
    ring_simplify.
    ring_simplify in Hweighted.
    exact Hweighted.
  }
  pose proof sm2_n_limbs_exact as
    [HN0 [HN1 [HN2 [HN3 HNvalue]]]].
  pose proof (u256_add_carry_chain
    out out_2 out_3 out_4
    SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
    out_5 out_6 out_7 out_8 retval_5 retval_6 retval_7 retval_8
    ltac:(lia) PreH15 PreH10 PreH5) as Hadd.
  rewrite <- HNvalue in Hadd.
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HR.
  pose proof sm2_n_bounds as HNbounds.
  assert (Hborrow : A_r_eq_b < B_r_eq_b) by lia.
  assert (Hcanonical : 0 <= A_r_eq_b - B_r_eq_b + SM2_N_Z < SM2_N_Z)
    by lia.
  assert (Hcases : retval_8 = 0 \/ retval_8 = 1) by lia.
  destruct Hcases as [Hzero | Hone].
  - subst retval_8; simpl in Hadd; lia.
  - rewrite Hone in Hadd.
    simpl in Hadd.
    change (u256_of_limbs out out_2 out_3 out_4 + SM2_N_Z =
      u256_of_limbs out_5 out_6 out_7 out_8 + U256_MOD) in Hadd.
    assert (Hresult : u256_of_limbs out_5 out_6 out_7 out_8 =
      A_r_eq_b - B_r_eq_b + SM2_N_Z) by lia.
    assert (Hmod : Zmod (A_r_eq_b - B_r_eq_b) SM2_N_Z =
      u256_of_limbs out_5 out_6 out_7 out_8).
    {
      rewrite Hresult.
      rewrite <- (Z.mod_add (A_r_eq_b - B_r_eq_b) 1 SM2_N_Z) by lia.
      rewrite Z.mod_small by exact Hcanonical.
      reflexivity.
    }
    subst b_pre.
    rewrite Hmod.
    unfold store_fn, store_mod, store_u256, store_sm2_n, store_u256_limbs.
    Exists x0 x1 x2 x3.
    Exists out_5 out_6 out_7 out_8.
    Exists SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
    entailer_with ltac:(assumption || lia).
    all: try lia.
    all: unfold UInt64Array.full, store_array;
      cbn [store_array_rec]; entailer!.
Qed. 

Lemma proof_of_sub_mod_n_return_wit_2_non_alias_split_goal_1 : sub_mod_n_return_wit_2_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_2_non_alias_split_goal_2 : sub_mod_n_return_wit_2_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_2_non_alias_split_goal_3 : sub_mod_n_return_wit_2_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_2_non_alias : sub_mod_n_return_wit_2_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || entailer!).
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  rewrite (unsigned_lnot_u64 x0_2 ltac:(lia)) in PreH41.
  rewrite (unsigned_lnot_u64 x1_2 ltac:(lia)) in PreH36.
  rewrite (unsigned_lnot_u64 x2_2 ltac:(lia)) in PreH31.
  rewrite (unsigned_lnot_u64 x3_2 ltac:(lia)) in PreH26.
  pose proof (addcarry4_weighted_bridge U64_MOD
    x0 x1 x2 x3
    (U64_MOD - x0_2) (U64_MOD - 1 - x1_2)
    (U64_MOD - 1 - x2_2) (U64_MOD - 1 - x3_2)
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    ltac:(lia) PreH36 PreH31 PreH26) as Hweighted.
  assert (Hdiff : A_non_alias - B_non_alias =
    u256_of_limbs out out_2 out_3 out_4 + (retval_4 - 1) * U256_MOD).
  {
    rewrite PreH51, PreH42.
    unfold u256_of_limbs.
    rewrite U256_MOD_as_U64_POW_4.
    unfold U64_POW.
    apply (proj1 (Z.add_cancel_r _ _ (U64_MOD ^ 4))).
    ring_simplify.
    ring_simplify in Hweighted.
    exact Hweighted.
  }
  pose proof sm2_n_limbs_exact as
    [HN0 [HN1 [HN2 [HN3 HNvalue]]]].
  pose proof (u256_add_carry_chain
    out out_2 out_3 out_4
    SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
    out_5 out_6 out_7 out_8 retval_5 retval_6 retval_7 retval_8
    ltac:(lia) PreH15 PreH10 PreH5) as Hadd.
  rewrite <- HNvalue in Hadd.
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof (u256_of_limbs_range out_5 out_6 out_7 out_8
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HR.
  pose proof sm2_n_bounds as HNbounds.
  assert (Hborrow : A_non_alias < B_non_alias) by lia.
  assert (Hcanonical : 0 <= A_non_alias - B_non_alias + SM2_N_Z < SM2_N_Z)
    by lia.
  assert (Hcases : retval_8 = 0 \/ retval_8 = 1) by lia.
  destruct Hcases as [Hzero | Hone].
  - subst retval_8; simpl in Hadd; lia.
  - rewrite Hone in Hadd.
    simpl in Hadd.
    change (u256_of_limbs out out_2 out_3 out_4 + SM2_N_Z =
      u256_of_limbs out_5 out_6 out_7 out_8 + U256_MOD) in Hadd.
    assert (Hresult : u256_of_limbs out_5 out_6 out_7 out_8 =
      A_non_alias - B_non_alias + SM2_N_Z) by lia.
    assert (Hmod : Zmod (A_non_alias - B_non_alias) SM2_N_Z =
      u256_of_limbs out_5 out_6 out_7 out_8).
    {
      rewrite Hresult.
      rewrite <- (Z.mod_add (A_non_alias - B_non_alias) 1 SM2_N_Z) by lia.
      rewrite Z.mod_small by exact Hcanonical.
      reflexivity.
    }
    rewrite Hmod.
    unfold store_fn, store_mod, store_u256, store_sm2_n, store_u256_limbs.
    Exists x0 x1 x2 x3.
    Exists x0_2 x1_2 x2_2 x3_2.
    Exists out_5 out_6 out_7 out_8.
    Exists SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
    entailer_with ltac:(assumption || lia).
    all: try lia.
    all: unfold UInt64Array.full, store_array;
      cbn [store_array_rec]; entailer!.
Qed. 

Lemma proof_of_sub_mod_n_return_wit_3_r_eq_b_split_goal_1 : sub_mod_n_return_wit_3_r_eq_b_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_3_r_eq_b_split_goal_2 : sub_mod_n_return_wit_3_r_eq_b_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_3_r_eq_b_split_goal_3 : sub_mod_n_return_wit_3_r_eq_b_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_3_r_eq_b : sub_mod_n_return_wit_3_r_eq_b.
Proof.
  LLM_pre_process ltac:(lia || nia || entailer!).
  rewrite (unsigned_lnot_u64 x0_2 ltac:(lia)) in PreH21.
  rewrite (unsigned_lnot_u64 x1_2 ltac:(lia)) in PreH16.
  rewrite (unsigned_lnot_u64 x2_2 ltac:(lia)) in PreH11.
  rewrite (unsigned_lnot_u64 x3_2 ltac:(lia)) in PreH6.
  pose proof (addcarry4_weighted_bridge U64_MOD
    x0 x1 x2 x3
    (U64_MOD - x0_2) (U64_MOD - 1 - x1_2)
    (U64_MOD - 1 - x2_2) (U64_MOD - 1 - x3_2)
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    ltac:(lia) PreH16 PreH11 PreH6) as Hweighted.
  assert (Hdiff : A_r_eq_b - B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4 + (retval_4 - 1) * U256_MOD).
  {
    rewrite PreH31, PreH22.
    unfold u256_of_limbs.
    rewrite U256_MOD_as_U64_POW_4.
    unfold U64_POW.
    apply (proj1 (Z.add_cancel_r _ _ (U64_MOD ^ 4))).
    ring_simplify.
    ring_simplify in Hweighted.
    exact Hweighted.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof sm2_n_bounds as HNbounds.
  pose proof sm2_n_limbs_exact as
    [HN0 [HN1 [HN2 [HN3 HNvalue]]]].
  assert (Hcarry : retval_4 = 1) by lia.
  assert (Hresult : A_r_eq_b - B_r_eq_b =
    u256_of_limbs out out_2 out_3 out_4) by lia.
  assert (Hcanonical : 0 <= A_r_eq_b - B_r_eq_b < SM2_N_Z) by lia.
  assert (Hmod : Zmod (A_r_eq_b - B_r_eq_b) SM2_N_Z =
    u256_of_limbs out out_2 out_3 out_4).
  {
    rewrite Z.mod_small by exact Hcanonical.
    exact Hresult.
  }
  subst b_pre.
  rewrite Hmod.
  unfold store_fn, store_mod, store_u256, store_sm2_n, store_u256_limbs.
  Exists x0 x1 x2 x3.
  Exists out out_2 out_3 out_4.
  Exists SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
  entailer_with ltac:(assumption || lia).
  all: try lia.
  all: unfold UInt64Array.full, store_array;
    cbn [store_array_rec]; entailer!.
Qed. 

Lemma proof_of_sub_mod_n_return_wit_4_non_alias_split_goal_1 : sub_mod_n_return_wit_4_non_alias_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_4_non_alias_split_goal_2 : sub_mod_n_return_wit_4_non_alias_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_4_non_alias_split_goal_3 : sub_mod_n_return_wit_4_non_alias_split_goal_3.
Proof. Abort.

Lemma proof_of_sub_mod_n_return_wit_4_non_alias : sub_mod_n_return_wit_4_non_alias.
Proof.
  LLM_pre_process ltac:(lia || nia || entailer!).
  rewrite (unsigned_lnot_u64 x0_2 ltac:(lia)) in PreH21.
  rewrite (unsigned_lnot_u64 x1_2 ltac:(lia)) in PreH16.
  rewrite (unsigned_lnot_u64 x2_2 ltac:(lia)) in PreH11.
  rewrite (unsigned_lnot_u64 x3_2 ltac:(lia)) in PreH6.
  pose proof (addcarry4_weighted_bridge U64_MOD
    x0 x1 x2 x3
    (U64_MOD - x0_2) (U64_MOD - 1 - x1_2)
    (U64_MOD - 1 - x2_2) (U64_MOD - 1 - x3_2)
    out out_2 out_3 out_4 retval retval_2 retval_3 retval_4
    ltac:(lia) PreH16 PreH11 PreH6) as Hweighted.
  assert (Hdiff : A_non_alias - B_non_alias =
    u256_of_limbs out out_2 out_3 out_4 + (retval_4 - 1) * U256_MOD).
  {
    rewrite PreH31, PreH22.
    unfold u256_of_limbs.
    rewrite U256_MOD_as_U64_POW_4.
    unfold U64_POW.
    apply (proj1 (Z.add_cancel_r _ _ (U64_MOD ^ 4))).
    ring_simplify.
    ring_simplify in Hweighted.
    exact Hweighted.
  }
  pose proof (u256_of_limbs_range out out_2 out_3 out_4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HD.
  pose proof sm2_n_bounds as HNbounds.
  pose proof sm2_n_limbs_exact as
    [HN0 [HN1 [HN2 [HN3 HNvalue]]]].
  assert (Hcarry : retval_4 = 1) by lia.
  assert (Hresult : A_non_alias - B_non_alias =
    u256_of_limbs out out_2 out_3 out_4) by lia.
  assert (Hcanonical : 0 <= A_non_alias - B_non_alias < SM2_N_Z) by lia.
  assert (Hmod : Zmod (A_non_alias - B_non_alias) SM2_N_Z =
    u256_of_limbs out out_2 out_3 out_4).
  {
    rewrite Z.mod_small by exact Hcanonical.
    exact Hresult.
  }
  rewrite Hmod.
  rewrite UInt64Array.undef_seg_empty.
  unfold store_fn, store_mod, store_u256, store_sm2_n, store_u256_limbs.
  Exists x0 x1 x2 x3.
  Exists x0_2 x1_2 x2_2 x3_2.
  Exists out out_2 out_3 out_4.
  Exists SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
  entailer_with ltac:(assumption || lia).
  all: try lia.
  all: unfold UInt64Array.full, store_array;
    cbn [store_array_rec]; entailer!.
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_1_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_1_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_1_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_1_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_1_r_eq_b_pure : sub_mod_n_partial_solve_wit_1_r_eq_b_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_2_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_2_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_2_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_2_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_2_non_alias_pure : sub_mod_n_partial_solve_wit_2_non_alias_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_3_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_3_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_3_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_3_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_3_r_eq_b_pure : sub_mod_n_partial_solve_wit_3_r_eq_b_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_4_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_4_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_4_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_4_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_4_non_alias_pure : sub_mod_n_partial_solve_wit_4_non_alias_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_5_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_5_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_5_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_5_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_5_r_eq_b_pure : sub_mod_n_partial_solve_wit_5_r_eq_b_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_6_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_6_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_6_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_6_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_6_non_alias_pure : sub_mod_n_partial_solve_wit_6_non_alias_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_7_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_7_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_7_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_7_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_7_r_eq_b_pure : sub_mod_n_partial_solve_wit_7_r_eq_b_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_8_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_8_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_8_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_8_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_8_non_alias_pure : sub_mod_n_partial_solve_wit_8_non_alias_pure.
Proof. solve_sub_mod_n_partial. Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_10_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_10_r_eq_b_pure : sub_mod_n_partial_solve_wit_10_r_eq_b_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_12_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_12_non_alias_pure : sub_mod_n_partial_solve_wit_12_non_alias_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_14_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_14_r_eq_b_pure : sub_mod_n_partial_solve_wit_14_r_eq_b_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_16_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_16_non_alias_pure : sub_mod_n_partial_solve_wit_16_non_alias_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_18_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_18_r_eq_b_pure : sub_mod_n_partial_solve_wit_18_r_eq_b_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_20_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_20_non_alias_pure : sub_mod_n_partial_solve_wit_20_non_alias_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_1 : sub_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_2 : sub_mod_n_partial_solve_wit_22_r_eq_b_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_22_r_eq_b_pure : sub_mod_n_partial_solve_wit_22_r_eq_b_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

Lemma proof_of_sub_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_1 : sub_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_2 : sub_mod_n_partial_solve_wit_24_non_alias_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sub_mod_n_partial_solve_wit_24_non_alias_pure : sub_mod_n_partial_solve_wit_24_non_alias_pure.
Proof.
  solve_sub_mod_n_partial.
  all: repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia];
    entailer_with ltac:(pose proof sm2_n_limbs; lia).
Qed. 

