Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SumLib Require Import SumLib.

Import ListNotations.
Local Open Scope Z_scope.

(** Little-endian positional arithmetic over a limb base [base]. *)

(** The place value immediately above [count] base-[base] limbs. *)
Definition limb_radix (base count : Z) : Z :=
  base ^ count.

(** Little-endian interpretation: [x0 + x1*base + x2*base^2 + ...]. *)
Definition limb_list_value (base : Z) (xs : list Z) : Z :=
  sum (fun i => 0 <= i < Zlength xs)
      (fun i => Znth i xs 0 * limb_radix base i).

(** Every entry of [xs] is a valid base-[base] digit. *)
Definition limb_list_bounded (base : Z) (xs : list Z) : Prop :=
  forall i,
    0 <= i < Zlength xs ->
    0 <= Znth i xs 0 < base.

(** * Radix facts *)

Lemma limb_radix_zero :
  forall base,
    limb_radix base 0 = 1.
Proof.
  intros base.
  unfold limb_radix.
  reflexivity.
Qed.

Lemma limb_radix_succ :
  forall base count,
    0 <= count ->
    limb_radix base (count + 1) = limb_radix base count * base.
Proof.
  intros base count Hcount.
  unfold limb_radix.
  replace (count + 1) with (Z.succ count) by lia.
  rewrite Z.pow_succ_r by exact Hcount.
  ring.
Qed.

Lemma limb_radix_nonneg :
  forall base count,
    0 <= base ->
    0 <= limb_radix base count.
Proof.
  intros base count Hbase.
  unfold limb_radix.
  apply Z.pow_nonneg.
  exact Hbase.
Qed.

Lemma limb_radix_positive :
  forall base count,
    0 < base ->
    0 <= count ->
    0 < limb_radix base count.
Proof.
  intros base count Hbase Hcount.
  unfold limb_radix.
  apply Z.pow_pos_nonneg; assumption.
Qed.

(** Appending one base-[base] digit extends the coefficient range by one place. *)
Lemma coefficient_extend_bound :
  forall base count coefficient digit,
    1 < base ->
    0 <= count ->
    0 <= coefficient < base ^ count ->
    0 <= digit < base ->
    0 <= coefficient + digit * base ^ count < base ^ (count + 1).
Proof.
  intros base count coefficient digit
    Hbase Hcount Hcoefficient Hdigit.
  replace (count + 1) with (Z.succ count) by lia.
  rewrite Z.pow_succ_r by exact Hcount.
  pose proof
    (Z.pow_pos_nonneg base count ltac:(lia) Hcount)
    as Hpower.
  nia.
Qed.

(** * Positional uniqueness *)

Lemma radix_step_unique :
  forall base low1 high1 low2 high2,
    0 < base ->
    0 <= low1 < base ->
    0 <= low2 < base ->
    low1 + base * high1 = low2 + base * high2 ->
    low1 = low2 /\ high1 = high2.
Proof.
  intros base low1 high1 low2 high2 Hbase Hlow1 Hlow2 Heq.
  assert (Hlow2mod : low2 = (low1 + base * high1) mod base).
  {
    rewrite Heq.
    apply (Zmod_unique _ _ high2 low2); nia.
  }
  assert (Hlow1mod : low1 = (low1 + base * high1) mod base).
  {
    apply (Zmod_unique _ _ high1 low1); nia.
  }
  split; nia.
Qed.

Lemma canonical_residue_from_decomposition :
  forall modulus value residue quotient,
    0 < modulus ->
    0 <= residue < modulus ->
    value = residue + quotient * modulus ->
    Z.modulo value modulus = residue.
Proof.
  intros modulus value residue quotient Hmodulus Hresidue Hdecomp.
  symmetry.
  apply Z.mod_unique with (q := quotient).
  - left.
    exact Hresidue.
  - rewrite Hdecomp.
    rewrite Z.mul_comm.
    apply Z.add_comm.
Qed.

(** * List structure *)

Lemma limb_list_value_nil :
  forall base,
    limb_list_value base nil = 0.
Proof.
  intros base.
  unfold limb_list_value.
  rewrite Zlength_nil.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.

Lemma limb_list_value_cons :
  forall base x xs,
    limb_list_value base (x :: xs) =
      x + base * limb_list_value base xs.
Proof.
  intros base x xs.
  unfold limb_list_value.
  rewrite
    (sum_Z_range_Znth_cons_indexed
      0 x xs (fun i digit => digit * limb_radix base i)).
  rewrite limb_radix_zero.
  replace (x * 1) with x by ring.
  rewrite <- sum_Z_range_factor_l.
  f_equal.
  apply sum_Z_range_ext.
  intros i Hi.
  rewrite limb_radix_succ by lia.
  ring.
Qed.

Lemma limb_list_bounded_cons_iff :
  forall base x xs,
    limb_list_bounded base (x :: xs) <->
      0 <= x < base /\ limb_list_bounded base xs.
Proof.
  intros base x xs.
  pose proof (Zlength_nonneg xs) as Hlength.
  split.
  - intros Hbounded.
    split.
    + specialize (Hbounded 0).
      rewrite Zlength_cons in Hbounded.
      specialize (Hbounded ltac:(lia)).
      rewrite Znth0_cons in Hbounded.
      exact Hbounded.
    + intros i Hi.
      specialize (Hbounded (i + 1)).
      rewrite Zlength_cons in Hbounded.
      specialize (Hbounded ltac:(lia)).
      rewrite Znth_cons in Hbounded by lia.
      replace (i + 1 - 1) with i in Hbounded by lia.
      exact Hbounded.
  - intros [Hx Hxs] i Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons.
      exact Hx.
    + rewrite Znth_cons by lia.
      apply Hxs.
      rewrite Zlength_cons in Hi.
      lia.
Qed.

Lemma limb_list_bounded_app :
  forall base xs ys,
    limb_list_bounded base (xs ++ ys) <->
      limb_list_bounded base xs /\ limb_list_bounded base ys.
Proof.
  intros base xs.
  induction xs as [|x xs IH]; intros ys.
  - cbn.
    split.
    + intros Hbounded.
      split.
      * unfold limb_list_bounded.
        intros i Hi.
        rewrite Zlength_nil in Hi.
        lia.
      * exact Hbounded.
    + intros [_ Hbounded].
      exact Hbounded.
  - cbn [app].
    rewrite !limb_list_bounded_cons_iff, IH.
    tauto.
Qed.

Lemma limb_list_bounded_rev :
  forall base xs,
    limb_list_bounded base (rev xs) <-> limb_list_bounded base xs.
Proof.
  intros base xs.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [rev].
    rewrite limb_list_bounded_app, limb_list_bounded_cons_iff, IH.
    split.
    + intros [Hxs [Hx _]].
      apply (proj2 (limb_list_bounded_cons_iff base x xs)).
      split; assumption.
    + intros Hbounded.
      apply (proj1 (limb_list_bounded_cons_iff base x xs)) in Hbounded.
      destruct Hbounded as [Hx Hxs].
      split; [exact Hxs |].
      split; [exact Hx |].
      unfold limb_list_bounded.
      intros index Hindex.
      rewrite Zlength_nil in Hindex.
      lia.
Qed.

Lemma limb_list_bounded_sublist :
  forall base xs lo hi,
    limb_list_bounded base xs ->
    0 <= lo <= hi /\ hi <= Zlength xs ->
    limb_list_bounded base (sublist lo hi xs).
Proof.
  intros base xs lo hi Hbounded Hrange i Hi.
  rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia.
  apply Hbounded.
  lia.
Qed.

Lemma limb_list_value_app :
  forall base xs ys,
    limb_list_value base (xs ++ ys) =
      limb_list_value base xs +
      limb_list_value base ys * limb_radix base (Zlength xs).
Proof.
  intros base xs ys.
  unfold limb_list_value.
  rewrite
    (sum_Z_range_Znth_app_indexed
      0 xs ys (fun i digit => digit * limb_radix base i)).
  f_equal.
  rewrite <- sum_Z_range_factor_r.
  apply sum_Z_range_ext.
  intros i Hi.
  unfold limb_radix.
  rewrite Z.pow_add_r by (pose proof (Zlength_nonneg xs); lia).
  ring.
Qed.

(**
 * Split a positional value at any valid limb boundary.
 *
 * The high slice is rebased to start at exponent zero; [limb_radix base split]
 * restores its original place value.
 *)
Lemma limb_list_value_split :
  forall base xs split,
    0 <= split <= Zlength xs ->
    limb_list_value base xs =
      limb_list_value base (sublist 0 split xs) +
      limb_list_value base (sublist split (Zlength xs) xs) *
        limb_radix base split.
Proof.
  intros base xs split Hsplit.
  assert (Hparts :
    xs =
      sublist 0 split xs ++
      sublist split (Zlength xs) xs).
  {
    rewrite <-
      (sublist_self xs (Zlength xs) ltac:(reflexivity)) at 1.
    apply sublist_split; lia.
  }
  rewrite Hparts at 1.
  rewrite limb_list_value_app.
  rewrite Zlength_sublist0 by lia.
  reflexivity.
Qed.

(** * Bounds *)

Lemma limb_list_value_nonneg :
  forall base xs,
    0 <= base ->
    limb_list_bounded base xs ->
    0 <= limb_list_value base xs.
Proof.
  intros base xs Hbase Hbounded.
  unfold limb_list_value.
  apply sum_nonneg.
  intros i Hi.
  specialize (Hbounded i Hi).
  pose proof (limb_radix_nonneg base i Hbase).
  nia.
Qed.

Lemma limb_list_value_range :
  forall base xs,
    1 < base ->
    limb_list_bounded base xs ->
    0 <= limb_list_value base xs <
      limb_radix base (Zlength xs).
Proof.
  intros base xs.
  induction xs as [|x xs IH]; intros Hbase Hbounded.
  - rewrite limb_list_value_nil, Zlength_nil, limb_radix_zero.
    lia.
  - rewrite limb_list_bounded_cons_iff in Hbounded.
    destruct Hbounded as [Hx Hxs].
    specialize (IH Hbase Hxs).
    rewrite limb_list_value_cons, Zlength_cons.
    replace (Z.succ (Zlength xs)) with (Zlength xs + 1) by lia.
    rewrite limb_radix_succ by apply Zlength_nonneg.
    pose proof
      (limb_radix_positive base (Zlength xs) ltac:(lia)
        (Zlength_nonneg xs)).
    nia.
Qed.

(** Extracting one digit from a bounded little-endian positional value. *)
Lemma limb_list_value_digit :
  forall base xs index,
    1 < base ->
    limb_list_bounded base xs ->
    0 <= index < Zlength xs ->
    (limb_list_value base xs / limb_radix base index) mod base =
      Znth index xs 0.
Proof.
  intros base xs index Hbase Hbounded Hindex.
  pose proof
    (limb_list_value_split base xs index ltac:(lia)) as Hsplit.
  assert (Hprefix_bounded :
    limb_list_bounded base (sublist 0 index xs)).
  {
    intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hbounded.
    lia.
  }
  pose proof
    (limb_list_value_range
      base (sublist 0 index xs) Hbase Hprefix_bounded) as Hprefix.
  rewrite Zlength_sublist in Hprefix by lia.
  replace (index - 0) with index in Hprefix by lia.
  destruct (sublist index (Zlength xs) xs) as [|digit tail]
    eqn:Hsuffix.
  {
    pose proof
      (Zlength_sublist index (Zlength xs) xs ltac:(lia)) as Hlength.
    rewrite Hsuffix, Zlength_nil in Hlength.
    lia.
  }
  assert (Hdigit : digit = Znth index xs 0).
  {
    pose proof
      (Znth_sublist 0 index 0 (Zlength xs) xs
        ltac:(lia) ltac:(lia)) as Hnth.
    rewrite Hsuffix, Znth0_cons in Hnth.
    replace (0 + index) with index in Hnth by lia.
    exact Hnth.
  }
  assert (Hdigit_range : 0 <= digit < base).
  {
    rewrite Hdigit.
    apply Hbounded.
    exact Hindex.
  }
  rewrite limb_list_value_cons in Hsplit.
  assert (Hdiv :
    limb_list_value base xs / limb_radix base index =
      digit + base * limb_list_value base tail).
  {
    symmetry.
    apply Z.div_unique with
      (r := limb_list_value base (sublist 0 index xs)).
    - left.
      exact Hprefix.
    - rewrite Hsplit.
      ring.
  }
  rewrite Hdiv, <- Hdigit.
  symmetry.
  apply Z.mod_unique with (q := limb_list_value base tail).
  - left.
    exact Hdigit_range.
  - ring.
Qed.

Lemma limb_digit_pair_range :
  forall base low high,
    1 < base ->
    0 <= low < base ->
    0 <= high < base ->
    0 <= low + high * base < limb_radix base 2.
Proof.
  intros base low high Hbase Hlow Hhigh.
  unfold limb_radix.
  replace (base ^ 2) with (base * base) by ring.
  nia.
Qed.

Lemma limb_digit_product_range :
  forall base left right,
    0 <= base ->
    0 <= left < base ->
    0 <= right < base ->
    0 <= left * right < limb_radix base 2.
Proof.
  intros base left right Hbase Hleft Hright.
  unfold limb_radix.
  replace (base ^ 2) with (base * base) by ring.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** * Point updates and carry propagation *)

Lemma limb_list_bounded_replace_Znth :
  forall base xs index value,
    limb_list_bounded base xs ->
    0 <= index < Zlength xs ->
    0 <= value < base ->
    limb_list_bounded base (replace_Znth index value xs).
Proof.
  intros base xs index value Hbounded Hindex Hvalue.
  unfold limb_list_bounded in *.
  intros i Hi.
  rewrite Zlength_replace_Znth in Hi.
  destruct (Z.eq_dec i index) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by exact Hindex.
    exact Hvalue.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hbounded.
    exact Hi.
Qed.

Lemma limb_list_value_replace_Znth :
  forall base xs index value,
    0 <= index < Zlength xs ->
    limb_list_value base (replace_Znth index value xs) =
      limb_list_value base xs +
      (value - Znth index xs 0) * limb_radix base index.
Proof.
  intros base xs index value Hindex.
  assert (Hprefix :
    sum (fun i => 0 <= i < index)
        (fun i =>
          Znth i (replace_Znth index value xs) 0 * limb_radix base i) =
    sum (fun i => 0 <= i < index)
        (fun i => Znth i xs 0 * limb_radix base i)).
  {
    apply sum_ext.
    intros i Hi.
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  assert (Hsuffix :
    sum (fun i => index + 1 <= i < Zlength xs)
        (fun i =>
          Znth i (replace_Znth index value xs) 0 * limb_radix base i) =
    sum (fun i => index + 1 <= i < Zlength xs)
        (fun i => Znth i xs 0 * limb_radix base i)).
  {
    apply sum_ext.
    intros i Hi.
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  unfold limb_list_value.
  rewrite Zlength_replace_Znth.
  rewrite
    (sum_Z_range_split 0 index (Zlength xs)
      (fun i =>
        Znth i (replace_Znth index value xs) 0 * limb_radix base i))
    by lia.
  rewrite
    (sum_Z_range_cons index (Zlength xs)
      (fun i =>
        Znth i (replace_Znth index value xs) 0 * limb_radix base i))
    by lia.
  rewrite
    (sum_Z_range_split 0 index (Zlength xs)
      (fun i => Znth i xs 0 * limb_radix base i))
    by lia.
  rewrite
    (sum_Z_range_cons index (Zlength xs)
      (fun i => Znth i xs 0 * limb_radix base i))
    by lia.
  rewrite Hprefix, Hsuffix.
  rewrite Znth_replace_Znth_Same by exact Hindex.
  ring.
Qed.

Lemma limb_list_value_carry_step :
  forall base xs position carry output next,
    0 <= position < Zlength xs ->
    Znth position xs 0 + carry = output + next * base ->
    limb_list_value base (replace_Znth position output xs) +
      next * limb_radix base (position + 1) =
    limb_list_value base xs +
      carry * limb_radix base position.
Proof.
  intros base xs position carry output next Hposition Hstep.
  rewrite limb_list_value_replace_Znth by exact Hposition.
  rewrite limb_radix_succ by lia.
  assert (
    output - Znth position xs 0 + next * base = carry) by lia.
  nia.
Qed.
