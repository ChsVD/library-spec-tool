(** Loop-level mathematics for the ordinary fixed-base SM2 multiplier. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Export byte_memory.
From SimpleC.EE.Applications_human.sm2.lib Require Import
  sm2_curve sm2_generator_order ecc sm2_ecc_const_table.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Import Snaive_C_Rules.
Local Open Scope sac.

(** The integer represented by the first [count] little-endian bytes. *)
Definition sm2_scalar_prefix (scalar count : Z) : Z :=
  scalar mod SM2_BYTE_BASE ^ count.

(** The contribution accumulated in one 64-bit limb after [count] bytes. *)
Definition sm2_scalar_chunk (scalar limb count : Z) : Z :=
  sm2_scalar_prefix scalar (8 * limb + count) -
  sm2_scalar_prefix scalar (8 * limb).

(** The table entry selected by byte [byte_in_limb] of limb [limb]. *)
Definition sm2_scalar_term (scalar limb byte_in_limb : Z) : Z :=
  sm2_scalar_byte scalar (8 * limb + byte_in_limb) *
  SM2_BYTE_BASE ^ (8 * limb + byte_in_limb).

(** The weighted scalar contribution selected by a concrete table byte. *)
Definition sm2_table_term (byte_value limb byte_in_limb : Z) : Z :=
  byte_value * SM2_BYTE_BASE ^ (8 * limb + byte_in_limb).

Lemma sm2_byte_power_positive :
  forall exponent,
    0 <= exponent ->
    0 < SM2_BYTE_BASE ^ exponent.
Proof.
  intros exponent Hexponent.
  apply Z.pow_pos_nonneg.
  - exact sm2_byte_base_positive.
  - exact Hexponent.
Qed.

Lemma sm2_scalar_byte_from_list :
  forall scalar bytes index,
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = scalar ->
    0 <= index < 32 ->
    Znth index bytes 0 = sm2_scalar_byte scalar index.
Proof.
  intros scalar bytes index Hlength Hbounded Hvalue Hindex.
  unfold sm2_scalar_byte, u8_list_value, u8_list_bounded in *.
  rewrite <- Hvalue.
  symmetry.
  apply limb_list_value_digit.
  - unfold SM2_BYTE_BASE.
    lia.
  - exact Hbounded.
  - rewrite Hlength.
    exact Hindex.
Qed.

Lemma sm2_scalar_byte_from_chunk :
  forall scalar bytes limb index,
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = scalar ->
    0 <= limb < 4 ->
    0 <= index < 8 ->
    Znth index (sublist (8 * limb) (8 * limb + 8) bytes) 0 =
      sm2_scalar_byte scalar (8 * limb + index).
Proof.
  intros scalar bytes limb index Hlength Hbounded Hvalue Hlimb Hindex.
  rewrite Znth_sublist by lia.
  replace (8 * limb + index) with (index + 8 * limb) by lia.
  apply sm2_scalar_byte_from_list; try assumption.
  lia.
Qed.

Lemma sm2_table_term_from_chunk :
  forall scalar bytes limb index,
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = scalar ->
    0 <= limb < 4 ->
    0 <= index < 8 ->
    sm2_table_term
      (Znth index (sublist (8 * limb) (8 * limb + 8) bytes) 0)
      limb index =
    sm2_scalar_term scalar limb index.
Proof.
  intros scalar bytes limb index Hlength Hbounded Hvalue Hlimb Hindex.
  unfold sm2_table_term, sm2_scalar_term.
  rewrite (sm2_scalar_byte_from_chunk scalar bytes limb index)
    by assumption.
  reflexivity.
Qed.


(** Repackage three four-limb coordinate arrays at the fixed-base loop
    initialization boundary. *)
Lemma uint64_full4_triplet_to_store_jpoint_fields :
  forall address xs ys zs,
    0 <= u64_list_value xs < SM2_P_Z ->
    0 <= u64_list_value ys < SM2_P_Z ->
    0 <= u64_list_value zs < SM2_P_Z ->
    UInt64Array.full (&(address # "JPoint" ->ₛ "z" .ₛ "v")) 4 zs **
    UInt64Array.full (&(address # "JPoint" ->ₛ "y" .ₛ "v")) 4 ys **
    UInt64Array.full (&(address # "JPoint" ->ₛ "x" .ₛ "v")) 4 xs |--
      store_jpoint_fields address
        (u64_list_value xs) (u64_list_value ys) (u64_list_value zs).
Proof.
  intros address xs ys zs Hx Hy Hz.
  repeat sep_apply uint64_full4_to_store_u256_limbs.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!; csimpl; entailer!.
Qed.

Lemma uint64_full4_named_triplet_to_store_jpoint_fields :
  forall name xs ys zs,
    0 <= u64_list_value xs < SM2_P_Z ->
    0 <= u64_list_value ys < SM2_P_Z ->
    0 <= u64_list_value zs < SM2_P_Z ->
    UInt64Array.full
      (eval_addr_expr
        (RE_addr_of
          (LE_dot_field
            (LE_arrow_field (RE_addr_of (LE_var name)) "z")
            "v"))) 4 zs **
    UInt64Array.full
      (eval_addr_expr
        (RE_addr_of
          (LE_dot_field
            (LE_arrow_field (RE_addr_of (LE_var name)) "y")
            "v"))) 4 ys **
    UInt64Array.full
      (eval_addr_expr
        (RE_addr_of
          (LE_dot_field
            (LE_arrow_field (RE_addr_of (LE_var name)) "x")
            "v"))) 4 xs |--
      store_jpoint_fields (eval_addr_expr (RE_addr_of (LE_var name)))
        (u64_list_value xs) (u64_list_value ys) (u64_list_value zs).
Proof.
  intros name xs ys zs Hx Hy Hz.
  rewrite (named_jpoint_u32_v_addr_eq name "x").
  rewrite (named_jpoint_u32_v_addr_eq name "y").
  rewrite (named_jpoint_u32_v_addr_eq name "z").
  repeat sep_apply uint64_full4_to_store_u256_limbs.
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!; csimpl; entailer!.
Qed.

Lemma store_u256_limbs_named_zxy_to_store_jpoint_fields :
  forall name x y z,
    0 <= x < SM2_P_Z ->
    0 <= y < SM2_P_Z ->
    0 <= z < SM2_P_Z ->
    store_u256_limbs
      (eval_addr_expr
        (RE_addr_of
          (LE_dot_field
            (LE_arrow_field (RE_addr_of (LE_var name)) "z")
            "v"))) z **
    store_u256_limbs
      (eval_addr_expr
        (RE_addr_of
          (LE_dot_field
            (LE_arrow_field (RE_addr_of (LE_var name)) "x")
            "v"))) x **
    store_u256_limbs
      (eval_addr_expr
        (RE_addr_of
          (LE_dot_field
            (LE_arrow_field (RE_addr_of (LE_var name)) "y")
            "v"))) y |--
      store_jpoint_fields (eval_addr_expr (RE_addr_of (LE_var name))) x y z.
Proof.
  intros name x y z Hx Hy Hz.
  rewrite (named_jpoint_u32_v_addr_eq name "x").
  rewrite (named_jpoint_u32_v_addr_eq name "y").
  rewrite (named_jpoint_u32_v_addr_eq name "z").
  unfold store_jpoint_fields, store_fp, store_mod, store_u256.
  entailer!.
  rewrite (nested_jpoint_u32_v_addr_eq &(name) "x").
  rewrite (nested_jpoint_u32_v_addr_eq &(name) "y").
  rewrite (nested_jpoint_u32_v_addr_eq &(name) "z").
  entailer!.
Qed.

(** A generated AFPoint record whose fields contain Montgomery coordinates. *)
Lemma StructPredAFPoint_to_store_mont_afpoint :
  forall address record x y point,
    afpoint_represents x y point ->
    sm2_record_x record = mont_p x ->
    sm2_record_y record = mont_p y ->
    StructPredAFPoint address record |--
      store_mont_afpoint address point.
Proof.
  intros address record x y point Hrepresents Hx Hy.
  pose proof (afpoint_represents_bounds _ _ _ Hrepresents)
    as [Hx_range Hy_range].
  unfold StructPredAFPoint, StructPredu32.
  sep_apply uint64_full4_to_store_u256_limbs.
  sep_apply uint64_full4_to_store_u256_limbs.
  unfold store_mont_afpoint, store_mont_afpoint_coords,
    store_afpoint_fields, store_fp, store_mod, store_u256.
  Exists x y.
  unfold sm2_record_x, sm2_record_y in Hx, Hy.
  entailer!; csimpl; entailer!.
  - rewrite Hx, Hy. cancel.
  - exact (proj1 (mont_p_range y)).
  - exact (proj2 (mont_p_range y)).
  - exact (proj1 (mont_p_range x)).
  - exact (proj2 (mont_p_range x)).
Qed.

Lemma store_mont_afpoint_to_StructPredAFPoint :
  forall address record x y point,
    record_afpoint_well_formed record ->
    afpoint_represents x y point ->
    sm2_record_x record = mont_p x ->
    sm2_record_y record = mont_p y ->
    store_mont_afpoint address point |--
      StructPredAFPoint address record.
Proof.
  intros address record x y point Hwell_formed Hrepresents Hx Hy.
  unfold store_mont_afpoint.
  Intros stored_x stored_y.
  destruct (afpoint_represents_functional
    stored_x stored_y x y point H Hrepresents) as [-> ->].
  unfold store_mont_afpoint_coords.
  Intros.
  rewrite <- Hx, <- Hy.
  apply store_afpoint_fields_to_StructPredAFPoint.
  exact Hwell_formed.
Qed.

Lemma sm2_scalar_prefix_bounds :
  forall scalar count,
    0 <= count ->
    0 <= sm2_scalar_prefix scalar count < SM2_BYTE_BASE ^ count.
Proof.
  intros scalar count Hcount.
  unfold sm2_scalar_prefix.
  apply Z.mod_pos_bound.
  now apply sm2_byte_power_positive.
Qed.

Lemma sm2_scalar_prefix_succ :
  forall scalar count,
    0 <= count ->
    sm2_scalar_prefix scalar (count + 1) =
    sm2_scalar_prefix scalar count +
    sm2_scalar_byte scalar count * SM2_BYTE_BASE ^ count.
Proof.
  intros scalar count Hcount.
  pose proof (sm2_byte_power_positive count Hcount) as Hpower.
  pose proof
    (Z.div_mod scalar (SM2_BYTE_BASE ^ count) ltac:(lia)) as Hsplit.
  pose proof
    (Z.div_mod (scalar / SM2_BYTE_BASE ^ count)
      SM2_BYTE_BASE ltac:(unfold SM2_BYTE_BASE; lia)) as Hquotient.
  pose proof (sm2_scalar_prefix_bounds scalar count Hcount) as Hprefix.
  pose proof (sm2_scalar_byte_bounds scalar count Hcount) as Hbyte.
  unfold sm2_scalar_prefix, sm2_scalar_byte in *.
  rewrite Z.pow_add_r by lia.
  cbn [Z.pow].
  symmetry.
  apply Z.mod_unique with
    (q := scalar / SM2_BYTE_BASE ^ count / SM2_BYTE_BASE).
  - left; split; [nia |].
    nia.
  - nia.
Qed.

Lemma sm2_scalar_chunk_zero :
  forall scalar limb,
    sm2_scalar_chunk scalar limb 0 = 0.
Proof.
  intros scalar limb.
  unfold sm2_scalar_chunk.
  replace (8 * limb + 0) with (8 * limb) by lia.
  lia.
Qed.

Lemma sm2_scalar_chunk_first_limb :
  forall scalar count,
    sm2_scalar_chunk scalar 0 count = sm2_scalar_prefix scalar count.
Proof.
  intros scalar count.
  unfold sm2_scalar_chunk, sm2_scalar_prefix.
  replace (8 * 0 + count) with count by lia.
  replace (SM2_BYTE_BASE ^ (8 * 0)) with 1 by reflexivity.
  rewrite Z.mod_1_r.
  lia.
Qed.

Lemma sm2_scalar_chunk_succ :
  forall scalar limb count,
    0 <= limb ->
    0 <= count ->
    sm2_scalar_chunk scalar limb (count + 1) =
    sm2_scalar_chunk scalar limb count +
    sm2_scalar_term scalar limb count.
Proof.
  intros scalar limb count Hlimb Hcount.
  unfold sm2_scalar_chunk, sm2_scalar_term.
  replace (8 * limb + (count + 1)) with
    ((8 * limb + count) + 1) by lia.
  rewrite sm2_scalar_prefix_succ by lia.
  ring.
Qed.

Lemma sm2_scalar_chunk_one :
  forall scalar limb,
    0 <= limb ->
    sm2_scalar_chunk scalar limb 1 = sm2_scalar_term scalar limb 0.
Proof.
  intros scalar limb Hlimb.
  replace 1 with (0 + 1) by lia.
  rewrite sm2_scalar_chunk_succ by lia.
  rewrite sm2_scalar_chunk_zero.
  lia.
Qed.

Lemma sm2_scalar_chunk_bounds :
  forall scalar limb count,
    0 <= limb ->
    0 <= count ->
    0 <= sm2_scalar_chunk scalar limb count <
      SM2_BYTE_BASE ^ (8 * limb + count).
Proof.
  intros scalar limb count Hlimb Hcount.
  remember (Z.to_nat count) as count_nat eqn:Hcount_nat.
  assert (Hcount_eq : count = Z.of_nat count_nat).
  { subst count_nat. now rewrite Z2Nat.id. }
  subst count.
  clear Hcount_nat Hcount.
  induction count_nat as [|count_nat IH].
  - rewrite sm2_scalar_chunk_zero.
    cbn [Z.of_nat Z.add].
    split; [lia |].
    apply sm2_byte_power_positive; lia.
  - rewrite Nat2Z.inj_succ.
    change (Z.succ (Z.of_nat count_nat)) with (Z.of_nat count_nat + 1).
    rewrite sm2_scalar_chunk_succ by lia.
    pose proof
      (sm2_scalar_byte_bounds scalar
        (8 * limb + Z.of_nat count_nat) ltac:(lia)) as Hbyte.
    unfold sm2_scalar_term.
    replace (8 * limb + (Z.of_nat count_nat + 1)) with
      (Z.succ (8 * limb + Z.of_nat count_nat)) by lia.
    rewrite Z.pow_succ_r by lia.
    unfold SM2_BYTE_BASE in *.
    nia.
Qed.

Lemma sm2_scalar_term_bounds :
  forall scalar limb count,
    0 <= limb ->
    0 <= count ->
    0 <= sm2_scalar_term scalar limb count <
      SM2_BYTE_BASE ^ (8 * limb + count + 1).
Proof.
  intros scalar limb count Hlimb Hcount.
  pose proof
    (sm2_scalar_byte_bounds scalar (8 * limb + count) ltac:(lia))
    as Hbyte.
  pose proof
    (sm2_byte_power_positive (8 * limb + count) ltac:(lia))
    as Hpower.
  unfold sm2_scalar_term.
  replace (8 * limb + count + 1) with
    (Z.succ (8 * limb + count)) by lia.
  rewrite Z.pow_succ_r by lia.
  unfold SM2_BYTE_BASE in *.
  nia.
Qed.

Lemma sm2_scalar_chunk_le_scalar :
  forall scalar limb count,
    0 <= scalar ->
    0 <= limb ->
    0 <= count ->
    sm2_scalar_chunk scalar limb count <= scalar.
Proof.
  intros scalar limb count Hscalar Hlimb Hcount.
  pose proof
    (sm2_scalar_prefix_bounds scalar (8 * limb) ltac:(lia))
    as Hlow.
  pose proof
    (Z.mod_le scalar (SM2_BYTE_BASE ^ (8 * limb + count))
      Hscalar
      (sm2_byte_power_positive (8 * limb + count) ltac:(lia))) as Hhigh.
  unfold sm2_scalar_chunk, sm2_scalar_prefix in *.
  lia.
Qed.

Lemma sm2_scalar_chunk_lt_order :
  forall scalar limb count,
    0 <= scalar < SM2_N_Z ->
    0 <= limb ->
    0 <= count ->
    0 <= sm2_scalar_chunk scalar limb count < SM2_N_Z.
Proof.
  intros scalar limb count Hscalar Hlimb Hcount.
  split.
  - exact (proj1 (sm2_scalar_chunk_bounds scalar limb count Hlimb Hcount)).
  - pose proof
      (sm2_scalar_chunk_le_scalar scalar limb count
        (proj1 Hscalar) Hlimb Hcount).
    lia.
Qed.

Lemma sm2_scalar_term_lt_order :
  forall scalar limb count,
    0 <= scalar < SM2_N_Z ->
    0 <= limb ->
    0 <= count ->
    0 <= sm2_scalar_term scalar limb count < SM2_N_Z.
Proof.
  intros scalar limb count Hscalar Hlimb Hcount.
  pose proof
    (sm2_scalar_chunk_lt_order scalar limb (count + 1)
      Hscalar Hlimb ltac:(lia)) as Hnext.
  pose proof
    (proj1 (sm2_scalar_chunk_bounds scalar limb count Hlimb Hcount))
    as Hchunk.
  pose proof
    (proj1 (sm2_scalar_term_bounds scalar limb count Hlimb Hcount))
    as Hterm.
  pose proof
    (sm2_scalar_chunk_succ scalar limb count Hlimb Hcount) as Hstep.
  lia.
Qed.

Lemma sm2_scalar_chunk_term_distinct :
  forall scalar limb count,
    0 <= limb ->
    0 <= count ->
    sm2_scalar_term scalar limb count <> 0 ->
    sm2_scalar_chunk scalar limb count <
    sm2_scalar_term scalar limb count.
Proof.
  intros scalar limb count Hlimb Hcount Hterm.
  pose proof
    (sm2_scalar_chunk_bounds scalar limb count Hlimb Hcount) as Hchunk.
  pose proof
    (sm2_scalar_byte_bounds scalar (8 * limb + count) ltac:(lia))
    as Hbyte.
  pose proof
    (sm2_byte_power_positive (8 * limb + count) ltac:(lia))
    as Hpower.
  unfold sm2_scalar_term in *.
  assert (0 < sm2_scalar_byte scalar (8 * limb + count)) by nia.
  nia.
Qed.

Lemma sm2_inner_points_distinct :
  forall scalar limb count,
    0 <= scalar < SM2_N_Z ->
    0 <= limb ->
    0 <= count ->
    sm2_point_mul (sm2_scalar_chunk scalar limb count) SM2_G_POINT <>
      ECInfinity ->
    sm2_point_mul (sm2_scalar_term scalar limb count) SM2_G_POINT <>
      ECInfinity ->
    sm2_point_mul (sm2_scalar_chunk scalar limb count) SM2_G_POINT <>
    sm2_point_mul (sm2_scalar_term scalar limb count) SM2_G_POINT.
Proof.
  intros scalar limb count Hscalar Hlimb Hcount
    Hchunk_finite Hterm_finite Heq.
  assert (Hterm_nonzero : sm2_scalar_term scalar limb count <> 0).
  { intro Hzero.
    rewrite Hzero, sm2_point_mul_zero in Hterm_finite.
    contradiction. }
  pose proof
    (sm2_generator_mul_injective
      (sm2_scalar_chunk scalar limb count)
      (sm2_scalar_term scalar limb count)
      (sm2_scalar_chunk_lt_order scalar limb count Hscalar Hlimb Hcount)
      (sm2_scalar_term_lt_order scalar limb count Hscalar Hlimb Hcount)
      Heq) as Hscalar_eq.
  pose proof
    (sm2_scalar_chunk_term_distinct scalar limb count
      Hlimb Hcount Hterm_nonzero).
  lia.
Qed.

Lemma sm2_inner_sum_noninfinity :
  forall scalar limb count,
    0 <= scalar < SM2_N_Z ->
    0 <= limb ->
    0 <= count ->
    (sm2_point_mul (sm2_scalar_chunk scalar limb count) SM2_G_POINT <>
       ECInfinity \/
     sm2_point_mul (sm2_scalar_term scalar limb count) SM2_G_POINT <>
       ECInfinity) ->
    sm2_point_mul
      (sm2_scalar_chunk scalar limb count +
       sm2_scalar_term scalar limb count) SM2_G_POINT <>
    ECInfinity.
Proof.
  intros scalar limb count Hscalar Hlimb Hcount Hfinite.
  rewrite <- sm2_scalar_chunk_succ by lia.
  apply sm2_generator_exact_order.
  pose proof
    (sm2_scalar_chunk_lt_order scalar limb (count + 1)
      Hscalar Hlimb ltac:(lia)) as Hbounds.
  pose proof
    (sm2_scalar_chunk_succ scalar limb count Hlimb Hcount) as Hstep.
  pose proof
    (proj1 (sm2_scalar_chunk_bounds scalar limb count Hlimb Hcount))
    as Hchunk_nonnegative.
  pose proof
    (proj1 (sm2_scalar_term_bounds scalar limb count Hlimb Hcount))
    as Hterm_nonnegative.
  destruct Hfinite as [Hfinite | Hfinite].
  - destruct Hbounds as [Hnonnegative Hupper].
    assert (sm2_scalar_chunk scalar limb count <> 0).
    { intro Hzero.
      rewrite Hzero, sm2_point_mul_zero in Hfinite.
      contradiction. }
    lia.
  - assert (sm2_scalar_term scalar limb count <> 0).
    { intro Hzero.
      rewrite Hzero, sm2_point_mul_zero in Hfinite.
      contradiction. }
    lia.
Qed.

Lemma sm2_inner_add_step :
  forall scalar limb count,
    0 <= limb ->
    0 <= count ->
    sm2_point_add
      (sm2_point_mul (sm2_scalar_chunk scalar limb count) SM2_G_POINT)
      (sm2_point_mul (sm2_scalar_term scalar limb count) SM2_G_POINT) =
    sm2_point_mul
      (sm2_scalar_chunk scalar limb (count + 1)) SM2_G_POINT.
Proof.
  intros scalar limb count Hlimb Hcount.
  rewrite sm2_scalar_chunk_succ by lia.
  symmetry.
  apply sm2_point_mul_add.
  - exact (proj1 (sm2_scalar_chunk_bounds scalar limb count Hlimb Hcount)).
  - exact (proj1 (sm2_scalar_term_bounds scalar limb count Hlimb Hcount)).
Qed.

Lemma sm2_inner_add_step_from_chunk :
  forall scalar bytes limb count,
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = scalar ->
    0 <= limb < 4 ->
    0 <= count < 8 ->
    sm2_point_add
      (sm2_point_mul (sm2_scalar_chunk scalar limb count) SM2_G_POINT)
      (sm2_point_mul
        (sm2_table_term
          (Znth count (sublist (8 * limb) (8 * limb + 8) bytes) 0)
          limb count)
        SM2_G_POINT) =
    sm2_point_mul
      (sm2_scalar_chunk scalar limb (count + 1)) SM2_G_POINT.
Proof.
  intros scalar bytes limb count Hlength Hbounded Hvalue Hlimb Hcount.
  rewrite (sm2_table_term_from_chunk scalar bytes limb count)
    by assumption.
  apply sm2_inner_add_step; lia.
Qed.

Lemma sm2_scalar_chunk_one_from_chunk :
  forall scalar bytes limb,
    Zlength bytes = 32 ->
    u8_list_bounded bytes ->
    u8_list_value bytes = scalar ->
    0 <= limb < 4 ->
    sm2_table_term
      (Znth 0 (sublist (8 * limb) (8 * limb + 8) bytes) 0)
      limb 0 =
    sm2_scalar_chunk scalar limb 1.
Proof.
  intros scalar bytes limb Hlength Hbounded Hvalue Hlimb.
  rewrite (sm2_table_term_from_chunk scalar bytes limb 0)
    by (try assumption; lia).
  symmetry.
  apply sm2_scalar_chunk_one; lia.
Qed.

Lemma sm2_outer_prefix_step :
  forall scalar limb,
    0 <= limb ->
    sm2_point_add
      (sm2_point_mul (sm2_scalar_prefix scalar (8 * limb)) SM2_G_POINT)
      (sm2_point_mul (sm2_scalar_chunk scalar limb 8) SM2_G_POINT) =
    sm2_point_mul (sm2_scalar_prefix scalar (8 * (limb + 1)))
      SM2_G_POINT.
Proof.
  intros scalar limb Hlimb.
  unfold sm2_scalar_chunk.
  replace (8 * limb + 8) with (8 * (limb + 1)) by lia.
  symmetry.
  rewrite <- sm2_point_mul_add.
  - f_equal. lia.
  - exact (proj1 (sm2_scalar_prefix_bounds scalar (8 * limb) ltac:(lia))).
  - pose proof
      (proj1 (sm2_scalar_chunk_bounds scalar limb 8 Hlimb ltac:(lia)))
      as Hchunk.
    unfold sm2_scalar_chunk in Hchunk.
    replace (8 * limb + 8) with (8 * (limb + 1)) in Hchunk by lia.
    exact Hchunk.
Qed.

Lemma sm2_scalar_prefix_32 :
  forall scalar,
    0 <= scalar < SM2_N_Z ->
    sm2_scalar_prefix scalar 32 = scalar.
Proof.
  intros scalar Hscalar.
  unfold sm2_scalar_prefix, SM2_BYTE_BASE.
  apply Z.mod_small.
  pose proof sm2_n_bounds.
  change (0 <= scalar < U256_MOD).
  lia.
Qed.

Lemma sm2_table_point_at_scalar :
  forall limb byte_in_limb byte_value,
    0 <= limb ->
    0 <= byte_in_limb ->
    0 <= byte_value ->
    sm2_table_point_at SM2_BASE_TABLE_DATA
      (Z.to_nat limb) (Z.to_nat byte_in_limb) (Z.to_nat byte_value) =
    sm2_point_mul
      (byte_value * SM2_BYTE_BASE ^ (8 * limb + byte_in_limb))
      SM2_G_POINT.
Proof.
  intros limb byte_in_limb byte_value Hlimb Hbyte_in_limb Hbyte_value.
  unfold sm2_table_point_at, sm2_table_window_index,
    sm2_base_table_point, SM2_BYTE_BASE.
  rewrite !Z2Nat.id by assumption.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
  rewrite !Z2Nat.id by assumption.
  replace (Z.of_nat 8) with 8 by reflexivity.
  replace (limb * 8 + byte_in_limb) with
    (8 * limb + byte_in_limb) by ring.
  reflexivity.
Qed.

Definition sm2_mont_base_table_record_at
    (limb byte_in_limb byte_value : Z) : RecordAFPoint :=
  sm2_table_record SM2_MONT_BASE_TABLE_DATA
    (sm2_table_window_index
      (Z.to_nat limb) (Z.to_nat byte_in_limb))
    (Z.to_nat byte_value).

Lemma sm2_mont_base_table_flatten_record_at :
  forall limb byte_in_limb byte_value,
    0 <= limb < 4 ->
    0 <= byte_in_limb < 8 ->
    0 <= byte_value < 256 ->
    Znth (sm2_base_table_flat_index limb byte_in_limb byte_value)
      (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA) zero_record_afpoint =
    sm2_mont_base_table_record_at limb byte_in_limb byte_value.
Proof.
  intros limb byte_in_limb byte_value Hlimb Hbyte_in Hbyte.
  assert (Hlimb_nat : (Z.to_nat limb < 4)%nat).
  {
    change (Z.to_nat limb < Z.to_nat 4)%nat.
    apply (proj1 (Z2Nat.inj_lt limb 4 ltac:(lia) ltac:(lia))).
    lia.
  }
  assert (Hbyte_in_nat : (Z.to_nat byte_in_limb < 8)%nat).
  {
    change (Z.to_nat byte_in_limb < Z.to_nat 8)%nat.
    apply
      (proj1
        (Z2Nat.inj_lt byte_in_limb 8 ltac:(lia) ltac:(lia))).
    lia.
  }
  assert (Hbyte_nat : (Z.to_nat byte_value < 256)%nat).
  {
    change (Z.to_nat byte_value < Z.to_nat 256)%nat.
    apply
      (proj1
        (Z2Nat.inj_lt byte_value 256 ltac:(lia) ltac:(lia))).
    lia.
  }
  destruct sm2_mont_base_table_data_correct as [Hlength [Hrows _]].
  unfold sm2_base_table_flat_index, sm2_mont_base_table_record_at,
    sm2_table_record, sm2_table_window, sm2_table_window_index,
    sm2_table_flatten, Znth.
  rewrite Nat2Z.id.
  apply nth_concat_uniform.
  - exact Hrows.
  - unfold SM2_TABLE_WINDOWS in Hlength.
    rewrite Hlength.
    lia.
  - unfold SM2_TABLE_WINDOW_SIZE.
    exact Hbyte_nat.
Qed.

(** Extract one valid Montgomery fixed-base table record from its flattened
    generated array representation. *)
Lemma sm2_mont_base_table_extract_record :
  forall base limb byte_in_limb byte_value,
    0 <= limb < 4 ->
    0 <= byte_in_limb < 8 ->
    0 <= byte_value < 256 ->
    StructAFPointArray.full base SM2_TABLE_RECORDS
      (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA) |--
    StructPredAFPoint
      (base +
        sm2_base_table_flat_index limb byte_in_limb byte_value *
          StoreStructAFPointAsElement.sizeA)
      (sm2_mont_base_table_record_at limb byte_in_limb byte_value) **
    StructAFPointArray.missing_i base
      (sm2_base_table_flat_index limb byte_in_limb byte_value)
      0 SM2_TABLE_RECORDS
      (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA).
Proof.
  intros base limb byte_in_limb byte_value Hlimb Hbyte_in Hbyte.
  assert (Hindex :
    0 <= sm2_base_table_flat_index limb byte_in_limb byte_value <
      SM2_TABLE_RECORDS).
  {
    unfold sm2_base_table_flat_index.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul,
      Nat2Z.inj_add, Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia.
    unfold SM2_TABLE_RECORDS.
    nia.
  }
  transitivity
    (StructPredAFPoint
      (base +
        sm2_base_table_flat_index limb byte_in_limb byte_value *
          StoreStructAFPointAsElement.sizeA)
      (Znth (sm2_base_table_flat_index limb byte_in_limb byte_value)
        (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA)
        zero_record_afpoint) **
     StructAFPointArray.missing_i base
       (sm2_base_table_flat_index limb byte_in_limb byte_value)
       0 SM2_TABLE_RECORDS
       (sm2_table_flatten SM2_MONT_BASE_TABLE_DATA)).
  - apply StructAFPointArray.full_split_to_missing_i.
    exact Hindex.
  - rewrite (sm2_mont_base_table_flatten_record_at
      limb byte_in_limb byte_value Hlimb Hbyte_in Hbyte).
    apply derivable1_refl.
Qed.

(** Restore a generated AFPoint array after a single indexed record was
    extracted.  This is the common separation-logic boundary used by both
    fixed-base multiplication implementations. *)
Lemma struct_afpoint_array_missing_i_restore_full :
  forall base index length records,
    0 <= index < length ->
    Zlength records = length ->
    StructAFPointArray.missing_i base index 0 length records **
    StructPredAFPoint
      (base + index * StoreStructAFPointAsElement.sizeA)
      (Znth index records zero_record_afpoint) |--
    StructAFPointArray.full base length records.
Proof.
  intros base index length records Hindex Hlength.
  pose proof (StructAFPointArray.missing_i_merge_to_full
    base index length (Znth index records zero_record_afpoint) records
    Hindex) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge by lia.
  rewrite derivable1_sepcon_comm.
  exact Hmerge.
Qed.

Lemma sm2_base_table_record_at_represents :
  forall limb byte_in_limb byte_value,
    0 <= limb < 4 ->
    0 <= byte_in_limb < 8 ->
    0 <= byte_value < 256 ->
    afpoint_represents
      (sm2_record_x
        (sm2_base_table_record_at limb byte_in_limb byte_value))
      (sm2_record_y
        (sm2_base_table_record_at limb byte_in_limb byte_value))
      (sm2_point_mul
        (byte_value * SM2_BYTE_BASE ^ (8 * limb + byte_in_limb))
        SM2_G_POINT).
Proof.
  intros limb byte_in_limb byte_value Hlimb Hbyte_in Hbyte.
  destruct sm2_base_table_data_correct as [_ [_ Hcorrect]].
  unfold sm2_base_table_record_at.
  specialize
    (Hcorrect
      (sm2_table_window_index
        (Z.to_nat limb) (Z.to_nat byte_in_limb))
      (Z.to_nat byte_value)).
  assert (Hwindow :
    (sm2_table_window_index
      (Z.to_nat limb) (Z.to_nat byte_in_limb) <
      SM2_TABLE_WINDOWS)%nat).
  {
    unfold sm2_table_window_index, SM2_TABLE_WINDOWS.
    assert (Hlimb_nat : (Z.to_nat limb < 4)%nat).
    {
      change (Z.to_nat limb < Z.to_nat 4)%nat.
      apply (proj1 (Z2Nat.inj_lt limb 4 ltac:(lia) ltac:(lia))).
      lia.
    }
    assert (Hbyte_in_nat : (Z.to_nat byte_in_limb < 8)%nat).
    {
      change (Z.to_nat byte_in_limb < Z.to_nat 8)%nat.
      apply
        (proj1
          (Z2Nat.inj_lt byte_in_limb 8 ltac:(lia) ltac:(lia))).
      lia.
    }
    lia.
  }
  assert (Hbyte_nat : (Z.to_nat byte_value < SM2_TABLE_WINDOW_SIZE)%nat).
  {
    unfold SM2_TABLE_WINDOW_SIZE.
    change (Z.to_nat byte_value < Z.to_nat 256)%nat.
    apply (proj1 (Z2Nat.inj_lt byte_value 256 ltac:(lia) ltac:(lia))).
    lia.
  }
  specialize (Hcorrect Hwindow Hbyte_nat).
  change
    (afpoint_represents
      (sm2_record_x
        (sm2_table_record SM2_BASE_TABLE_DATA
          (sm2_table_window_index
            (Z.to_nat limb) (Z.to_nat byte_in_limb))
          (Z.to_nat byte_value)))
      (sm2_record_y
        (sm2_table_record SM2_BASE_TABLE_DATA
          (sm2_table_window_index
            (Z.to_nat limb) (Z.to_nat byte_in_limb))
          (Z.to_nat byte_value)))
      (sm2_table_point_at SM2_BASE_TABLE_DATA
        (Z.to_nat limb) (Z.to_nat byte_in_limb)
        (Z.to_nat byte_value))) in Hcorrect.
  rewrite (sm2_table_point_at_scalar
    limb byte_in_limb byte_value) in Hcorrect by lia.
  exact Hcorrect.
Qed.

Lemma sm2_mont_base_table_record_at_values :
  forall limb byte_in_limb byte_value,
    0 <= limb < 4 ->
    0 <= byte_in_limb < 8 ->
    0 <= byte_value < 256 ->
    sm2_record_x
      (sm2_mont_base_table_record_at limb byte_in_limb byte_value) =
      mont_p
        (sm2_record_x
          (sm2_base_table_record_at limb byte_in_limb byte_value)) /\
    sm2_record_y
      (sm2_mont_base_table_record_at limb byte_in_limb byte_value) =
      mont_p
        (sm2_record_y
          (sm2_base_table_record_at limb byte_in_limb byte_value)).
Proof.
  intros limb byte_in_limb byte_value Hlimb Hbyte_in Hbyte.
  destruct sm2_mont_base_table_data_correct as [_ [_ Hcorrect]].
  unfold sm2_mont_base_table_record_at, sm2_base_table_record_at.
  apply Hcorrect.
  - unfold sm2_table_window_index, SM2_TABLE_WINDOWS.
    assert (Hlimb_nat : (Z.to_nat limb < 4)%nat).
    {
      change (Z.to_nat limb < Z.to_nat 4)%nat.
      apply (proj1 (Z2Nat.inj_lt limb 4 ltac:(lia) ltac:(lia))).
      lia.
    }
    assert (Hbyte_in_nat : (Z.to_nat byte_in_limb < 8)%nat).
    {
      change (Z.to_nat byte_in_limb < Z.to_nat 8)%nat.
      apply
        (proj1
          (Z2Nat.inj_lt byte_in_limb 8 ltac:(lia) ltac:(lia))).
      lia.
    }
    lia.
  - unfold SM2_TABLE_WINDOW_SIZE.
    change (Z.to_nat byte_value < Z.to_nat 256)%nat.
    apply (proj1 (Z2Nat.inj_lt byte_value 256 ltac:(lia) ltac:(lia))).
    lia.
Qed.
