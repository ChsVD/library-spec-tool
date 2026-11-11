Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma array_bridges_strategy3_correctness : array_bridges_strategy3.
Proof.
  pre_process_default.
  subst q.
  sep_apply (UInt64Array.full_split_to_full p m n (repeat_Z x n)); try lia.
  assert (Hskipn_repeat :
    forall k total,
      (k <= total)%nat ->
      skipn k (repeat x total) = repeat x (total - k)).
  {
    intros k.
    induction k as [|k IH]; intros total Htotal.
    - simpl. now rewrite Nat.sub_0_r.
    - destruct total as [|total]; [lia |].
      simpl.
      apply IH.
      lia.
  }
  assert (Hsublist_repeat :
    sublist m n (repeat_Z x n) = repeat_Z x (n - m)).
  {
    unfold sublist, repeat_Z.
    replace (firstn (Z.to_nat n) (repeat x (Z.to_nat n)))
      with (repeat x (Z.to_nat n)).
    2: {
      symmetry.
      rewrite <- (repeat_length x (Z.to_nat n)) at 1.
      apply firstn_all.
    }
    rewrite Hskipn_repeat.
    - rewrite <- Z2Nat.inj_sub by lia.
      reflexivity.
    - apply (proj1 (Z2Nat.inj_le m n ltac:(lia) ltac:(lia))).
      lia.
  }
  rewrite Hsublist_repeat.
  sep_apply (UInt64Array.full_to_undef_full p m
    (sublist 0 m (repeat_Z x n))).
  entailer!.
  pre_process_default.
Qed.

Lemma array_bridges_strategy4_correctness : array_bridges_strategy4.
Proof.
  pre_process_default.
  subst q.
  sep_apply (UInt64Array.full_split_to_full p m n xs); try lia.
  sep_apply (UInt64Array.full_to_undef_full p m (sublist 0 m xs)).
  entailer!.
  pre_process_default.
Qed.

Lemma array_bridges_strategy5_correctness : array_bridges_strategy5.
Proof.
  pre_process_default.
  subst n; subst q; subst y.
  unfold UInt64Array.full, store_array, repeat_Z.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  cbn [repeat store_array_rec].
  replace (p + 0 * sizeof(UINT64)) with p by lia.
  entailer!.
Qed.

Lemma array_bridges_strategy7_correctness : array_bridges_strategy7.
Proof.
  pre_process_default.
  subst q.
  prop_apply (UInt64Array.full_Zlength p n xs).
  Intros.
  assert (Hrange : 0 <= Znth i xs 0 < U64_MOD).
  {
    unfold u64_list_bounded, limb_list_bounded in H.
    apply H.
    lia.
  }
  sep_apply_l_atomic (UInt64Array.full_split_to_missing_i p i n xs 0).
  - dump_pre_spatial.
    lia.
  - replace (p + i * 8) with (p + i * sizeof(UINT64))
      by (rewrite sizeof_uint64; lia).
    entailer!.
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    cancel.
Qed.

Lemma array_bridges_strategy10_correctness : array_bridges_strategy10.
Proof.
  pre_process_default.
  apply UInt64Array.full_shape_to_undef_full.
Qed.

Lemma array_bridges_strategy11_correctness : array_bridges_strategy11.
Proof.
  pre_process_default.
  subst q; subst m.
  replace (p + 0 * sizeof(UINT64)) with p by lia.
  reflexivity.
Qed.

Lemma array_bridges_strategy13_correctness : array_bridges_strategy13.
Proof.
  pre_process_default.
  subst q; subst m; subst ys.
  reflexivity.
Qed.

Lemma array_bridges_strategy1_correctness : array_bridges_strategy1.
Proof.
  pre_process_default.
  prop_apply (UInt64Array.full_Zlength p 4 xs).
  Intros.
  destruct xs as [|x0 xs].
  { rewrite Zlength_nil in H; lia. }
  rewrite Zlength_cons in H.
  destruct xs as [|x1 xs].
  { rewrite Zlength_nil in H; lia. }
  rewrite Zlength_cons in H.
  destruct xs as [|x2 xs].
  { rewrite Zlength_nil in H; lia. }
  rewrite Zlength_cons in H.
  destruct xs as [|x3 xs].
  { rewrite Zlength_nil in H; lia. }
  rewrite Zlength_cons in H.
  destruct xs as [|x4 xs].
  2: {
    rewrite Zlength_cons in H.
    pose proof (Zlength_nonneg xs).
    lia.
  }
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer!.
Qed.

Lemma array_bridges_strategy9_correctness : array_bridges_strategy9.
Proof.
  pre_process_default.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma array_bridges_strategy12_correctness : array_bridges_strategy12.
Proof.
  pre_process_default.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma array_bridges_strategy8_correctness : array_bridges_strategy8.
Proof.
  pre_process_default.
  assert (Hlength : Zlength (replace_Znth i v xs) = n).
  {
    rewrite Zlength_replace_Znth.
    lia.
  }
  assert (Hbounded : u64_list_bounded (replace_Znth i v xs)).
  {
    unfold u64_list_bounded in *.
    apply limb_list_bounded_replace_Znth.
    - assumption.
    - lia.
    - lia.
  }
  entailer!.
Qed.

Lemma array_bridges_strategy14_correctness : array_bridges_strategy14.
Proof.
  pre_process_default.
  subst n.
  prop_apply (UInt64Array.full_Zlength p 0 xs).
  Intros.
  apply Zlength_nil_inv in H.
  subst xs.
  rewrite UInt64Array.full_empty.
  entailer!.
Qed.

Lemma array_bridges_strategy2_correctness : array_bridges_strategy2.
Proof.
  pre_process_default.
  subst q.
  Intros.
  subst xs.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer!.
Qed.
