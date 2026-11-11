Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export sm2_common_lib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Import Snaive_C_Rules.
Local Open Scope sac.

(** * Carry arithmetic for portable and four-limb operations *)

Lemma addcarry64_mod_branches :
  forall cin a b : Z,
    0 <= cin <= 1 ->
    0 <= a < U64_MOD ->
    0 <= b < U64_MOD ->
    let m := U64_MOD in
    let s := (a + b) mod m in
    let r := (s + cin mod m) mod m in
    (r < s -> s < a ->
       0 <= r < m /\ 0 <= 1 <= 1 /\ a + b + cin = r + 1 * m) /\
    (r >= s -> s < a ->
       0 <= r < m /\ 0 <= 1 <= 1 /\ a + b + cin = r + 1 * m) /\
    (r < s -> s >= a ->
       0 <= r < m /\ 0 <= 1 <= 1 /\ a + b + cin = r + 1 * m) /\
    (r >= s -> s >= a ->
       0 <= r < m /\ 0 <= 0 <= 1 /\ a + b + cin = r + 0 * m).
Proof.
  intros cin a b Hcin Ha Hb.
  cbn zeta.
  set (m := U64_MOD) in *.
  assert (Hm : 1 < m) by (subst m; cbv [U64_MOD]; lia).
  assert (Hcinmod : cin mod m = cin) by (apply Z.mod_small; lia).
  rewrite Hcinmod.
  set (s := (a + b) mod m).
  set (r := (s + cin) mod m).
  assert (Hsrange : 0 <= s < m) by
    (subst s; apply Z.mod_pos_bound; lia).
  assert (Hrrange : 0 <= r < m) by
    (subst r; apply Z.mod_pos_bound; lia).
  assert (Hs_nowrap : a + b < m -> s = a + b).
  { intro H; subst s; apply Z.mod_small; lia. }
  assert (Hs_wrap : m <= a + b -> s = a + b - m).
  { intro H; subst s; symmetry; apply Z.mod_unique with (q := 1); lia. }
  assert (Hr_nowrap : s + cin < m -> r = s + cin).
  { intro H; subst r; apply Z.mod_small; lia. }
  assert (Hr_wrap : m <= s + cin -> r = s + cin - m).
  { intro H; subst r; symmetry; apply Z.mod_unique with (q := 1); lia. }
  assert (Hfirst_wrap : s < a -> s = a + b - m).
  { intro Hsa. destruct (Z_lt_ge_dec (a + b) m);
      [rewrite Hs_nowrap in Hsa by lia; lia | apply Hs_wrap; lia]. }
  assert (Hfirst_nowrap : s >= a -> s = a + b).
  { intro Hsa. destruct (Z_lt_ge_dec (a + b) m);
      [apply Hs_nowrap; lia | rewrite Hs_wrap in Hsa by lia; lia]. }
  assert (Hsecond_wrap : r < s -> r = s + cin - m).
  { intro Hrs. destruct (Z_lt_ge_dec (s + cin) m);
      [rewrite Hr_nowrap in Hrs by lia; lia | apply Hr_wrap; lia]. }
  assert (Hsecond_nowrap : r >= s -> r = s + cin).
  { intro Hrs. destruct (Z_lt_ge_dec (s + cin) m);
      [apply Hr_nowrap; lia | rewrite Hr_wrap in Hrs by lia; lia]. }
  repeat split; intros; try lia.
Qed.

Lemma u256_add_carry_chain :
  forall a0 a1 a2 a3 b0 b1 b2 b3
         t0 t1 t2 t3 c1 c2 c3 c4,
    a0 + b0 = t0 + c1 * U64_MOD ->
    a1 + b1 + c1 = t1 + c2 * U64_MOD ->
    a2 + b2 + c2 = t2 + c3 * U64_MOD ->
    a3 + b3 + c3 = t3 + c4 * U64_MOD ->
    u256_of_limbs a0 a1 a2 a3 + u256_of_limbs b0 b1 b2 b3 =
      u256_of_limbs t0 t1 t2 t3 + c4 * U256_MOD.
Proof.
  intros.
  cbv [u256_of_limbs U64_MOD U256_MOD] in *.
  lia.
Qed.

Lemma addcarry4_weighted_bridge : forall
    B a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c1 c2 c3 c4,
  a0 + b0 = r0 + c1 * B ->
  a1 + b1 + c1 = r1 + c2 * B ->
  a2 + b2 + c2 = r2 + c3 * B ->
  a3 + b3 + c3 = r3 + c4 * B ->
  (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3) +
  (b0 + b1 * B + b2 * B ^ 2 + b3 * B ^ 3) =
  (r0 + r1 * B + r2 * B ^ 2 + r3 * B ^ 3) + c4 * B ^ 4.
Proof.
  intros B a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c1 c2 c3 c4
    H0 H1 H2 H3.
  assert (E :
    ((a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3) +
     (b0 + b1 * B + b2 * B ^ 2 + b3 * B ^ 3) -
     ((r0 + r1 * B + r2 * B ^ 2 + r3 * B ^ 3) + c4 * B ^ 4)) =
    (a0 + b0 - (r0 + c1 * B)) +
    B * (a1 + b1 + c1 - (r1 + c2 * B)) +
    B ^ 2 * (a2 + b2 + c2 - (r2 + c3 * B)) +
    B ^ 3 * (a3 + b3 + c3 - (r3 + c4 * B))) by ring.
  rewrite H0, H1, H2, H3 in E.
  ring_simplify in E.
  lia.
Qed.

Lemma unsigned_lnot_u64 : forall x,
  0 <= x < U64_MOD ->
  unsigned_last_nbits (Z.lnot x) 64 = U64_MOD - 1 - x.
Proof.
  intros x Hx.
  unfold unsigned_last_nbits, U64_MOD in *.
  rewrite Z.lnot_eq_pred_opp.
  replace ((- x - 1) mod 2 ^ 64) with (2 ^ 64 - 1 - x).
  - lia.
  - apply Z.mod_unique with (-1); [lia | ring].
Qed.

Lemma unsigned_lnot_u64_range : forall x,
  0 <= x < U64_MOD ->
  0 <= unsigned_last_nbits (Z.lnot x) 64 < U64_MOD.
Proof.
  intros x Hx.
  rewrite unsigned_lnot_u64 by exact Hx.
  lia.
Qed.

Lemma u32_sub_chain4 : forall
    a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c1 c2 c3 c4,
  0 <= b0 < U64_MOD -> 0 <= b1 < U64_MOD ->
  0 <= b2 < U64_MOD -> 0 <= b3 < U64_MOD ->
  0 <= r0 < U64_MOD -> 0 <= r1 < U64_MOD ->
  0 <= r2 < U64_MOD -> 0 <= r3 < U64_MOD ->
  0 <= c4 <= 1 ->
  a0 + (U64_MOD - 1 - b0) + 1 = r0 + c1 * U64_MOD ->
  a1 + (U64_MOD - 1 - b1) + c1 = r1 + c2 * U64_MOD ->
  a2 + (U64_MOD - 1 - b2) + c2 = r2 + c3 * U64_MOD ->
  a3 + (U64_MOD - 1 - b3) + c3 = r3 + c4 * U64_MOD ->
  exists S borrow,
    0 <= S < U256_MOD /\ 0 <= borrow <= 1 /\
    u256_of_limbs a0 a1 a2 a3 - u256_of_limbs b0 b1 b2 b3 =
      S - borrow * U256_MOD /\
    S = u256_of_limbs r0 r1 r2 r3.
Proof.
  intros a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 c1 c2 c3 c4
    Hb0 Hb1 Hb2 Hb3 Hr0 Hr1 Hr2 Hr3 Hc4 E0 E1 E2 E3.
  exists (u256_of_limbs r0 r1 r2 r3), (1 - c4).
  split; [apply u256_of_limbs_range; assumption |].
  split; [lia |]. split; [| reflexivity].
  pose proof (addcarry4_weighted_bridge U64_MOD
    a0 a1 a2 a3
    (U64_MOD - b0) (U64_MOD - 1 - b1)
    (U64_MOD - 1 - b2) (U64_MOD - 1 - b3)
    r0 r1 r2 r3 c1 c2 c3 c4
    ltac:(lia) E1 E2 E3) as E.
  unfold u256_of_limbs in *.
  rewrite U256_MOD_as_U64_POW_4.
  unfold U64_POW.
  nia.
Qed.

(** * Left shift *)

Definition u256_shl_result (x y carry : Z) : Prop :=
  0 <= x < U256_MOD /\
  0 <= y < U256_MOD /\
  0 <= carry <= 1 /\
  2 * x = y + carry * U256_MOD.

Lemma u256_shl_result_no_overflow :
  forall x y carry,
    u256_shl_result x y carry ->
    2 * x < U256_MOD ->
    y = 2 * x /\ carry = 0.
Proof.
  intros x y carry Hshift Hbound.
  unfold u256_shl_result in Hshift.
  destruct Hshift as (_ & Hy & Hcarry & Heq).
  unfold U256_MOD in Hbound, Heq |- *.
  lia.
Qed.

Lemma u64_shift_components__shl_arithmetic :
  forall x,
    0 <= x < U64_MOD ->
    let low := unsigned_last_nbits (Z.shiftl x 1) 64 in
    let high := Z.shiftr x 63 in
    0 <= low <= U64_MOD - 2 /\
    0 <= high <= 1 /\
    2 * x = low + high * U64_MOD /\
    Z.land low 1 = 0.
Proof.
  intros x Hx.
  cbn zeta.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  unfold unsigned_last_nbits.
  unfold U64_MOD in Hx |- *.
  destruct (Z_lt_ge_dec x (2 ^ 63)) as [Hlo | Hhi].
  - assert (Hdiv : x / 2 ^ 63 = 0) by (apply Z.div_small; lia).
    assert (Hmod : x * 2 mod 2 ^ 64 = x * 2) by
      (apply Z.mod_small; lia).
    rewrite Hdiv, Hmod.
    repeat split; try lia.
    replace 1 with (Z.ones 1) by reflexivity.
    rewrite Z.land_ones by lia.
    change (x * 2 mod 2 = 0).
    apply Z.mod_mul; lia.
  - assert (Hdiv : x / 2 ^ 63 = 1).
    {
      symmetry.
      apply (Z.div_unique x (2 ^ 63) 1 (x - 2 ^ 63)); [left; lia | lia].
    }
    assert (Hmod : x * 2 mod 2 ^ 64 = x * 2 - 2 ^ 64).
    {
      symmetry.
      apply (Z.mod_unique (x * 2) (2 ^ 64) 1 (x * 2 - 2 ^ 64));
        [left; lia | lia].
    }
    rewrite Hdiv, Hmod.
    repeat split; try lia.
    replace 1 with (Z.ones 1) by reflexivity.
    rewrite Z.land_ones by lia.
    change ((x * 2 - 2 ^ 64) mod 2 = 0).
    replace (x * 2 - 2 ^ 64) with (2 * (x - 2 ^ 63)) by lia.
    rewrite Z.mul_comm.
    apply Z.mod_mul; lia.
Qed.

Lemma lor_low_carry__shl_arithmetic :
  forall low carry,
    Z.land low 1 = 0 ->
    0 <= carry <= 1 ->
    Z.lor low carry = low + carry.
Proof.
  intros low carry Hland Hcarry.
  assert (carry = 0 \/ carry = 1) by lia.
  destruct H as [-> | ->].
  - rewrite Z.lor_0_r; lia.
  - rewrite <- Z.lxor_lor by exact Hland.
    rewrite <- Z.add_nocarry_lxor by exact Hland.
    reflexivity.
Qed.

(** * Right shift *)

Lemma u64_lshift_lowbits_zero__u256_shift :
  forall a cnt,
    1 <= cnt < 64 ->
    (unsigned_last_nbits (a * 2 ^ cnt) 64) mod 2 ^ cnt = 0.
Proof.
  intros a cnt Hcnt.
  unfold unsigned_last_nbits.
  change (2 ^ 64) with U64_MOD.
  replace ((a * 2 ^ cnt) mod U64_MOD)
    with (a * 2 ^ cnt - U64_MOD * ((a * 2 ^ cnt) / U64_MOD)).
  2: {
    symmetry.
    apply Z.mod_eq.
    unfold U64_MOD; lia.
  }
  rewrite Zminus_mod.
  rewrite Z_mod_mult.
  assert (Hpow: U64_MOD = 2 ^ (64 - cnt) * 2 ^ cnt).
  {
    unfold U64_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (64 - cnt + cnt) with 64 by lia.
    reflexivity.
  }
  rewrite Hpow.
  rewrite Zmult_mod.
  rewrite Z_mod_mult.
  rewrite Z.mul_0_l.
  rewrite Z.sub_0_r.
  rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma u64_rshift_lor_add__u256_shift :
  forall low high cnt,
    0 <= low < U64_MOD ->
    1 <= cnt < 64 ->
    Z.lor (Z.shiftr low cnt)
      (unsigned_last_nbits (Z.shiftl high (64 - cnt)) 64) =
    Z.shiftr low cnt + unsigned_last_nbits (Z.shiftl high (64 - cnt)) 64.
Proof.
  intros low high cnt Hlow Hcnt.
  set (lo := Z.shiftr low cnt).
  set (hi := unsigned_last_nbits (Z.shiftl high (64 - cnt)) 64).
  assert (Hlo_bound: 0 <= lo < 2 ^ (64 - cnt)).
  {
    subst lo.
    rewrite Z.shiftr_div_pow2 by lia.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + replace (2 ^ cnt * 2 ^ (64 - cnt)) with U64_MOD.
        * lia.
        * unfold U64_MOD.
          rewrite <- Z.pow_add_r by lia.
          replace (cnt + (64 - cnt)) with 64 by lia.
          reflexivity.
  }
  assert (Hhi_mask: Z.land hi (Z.ones (64 - cnt)) = 0).
  {
    rewrite Z.land_ones by lia.
    subst hi.
    rewrite Z.shiftl_mul_pow2 by lia.
    apply u64_lshift_lowbits_zero__u256_shift.
    lia.
  }
  assert (Hland0: Z.land lo hi = 0).
  {
    replace lo with (Z.land lo (Z.ones (64 - cnt))).
    2: {
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    rewrite <- Z.land_assoc.
    rewrite (Z.land_comm (Z.ones (64 - cnt)) hi).
    rewrite Hhi_mask.
    apply Z.land_0_r.
  }
  rewrite <- Z.lxor_lor by exact Hland0.
  symmetry.
  apply Z.add_nocarry_lxor.
  exact Hland0.
Qed.

Lemma unsigned_last_nbits_shiftl_high__u256_shift :
  forall high cnt,
    0 <= high < U64_MOD ->
    1 <= cnt < 64 ->
    unsigned_last_nbits (Z.shiftl high (64 - cnt)) 64 =
      (high mod 2 ^ cnt) * 2 ^ (64 - cnt).
Proof.
  intros high cnt Hhigh Hcnt.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold unsigned_last_nbits.
  change (2 ^ 64) with U64_MOD.
  assert (Hpow: U64_MOD = 2 ^ cnt * 2 ^ (64 - cnt)).
  {
    unfold U64_MOD.
    rewrite <- Z.pow_add_r by lia.
    replace (cnt + (64 - cnt)) with 64 by lia.
    reflexivity.
  }
  rewrite Hpow.
  pose proof (Z.div_mod high (2 ^ cnt) ltac:(apply Z.pow_nonzero; lia)) as Hdm.
  rewrite Hdm at 1.
  replace ((2 ^ cnt * (high / 2 ^ cnt) + high mod 2 ^ cnt) * 2 ^ (64 - cnt))
    with ((high mod 2 ^ cnt) * 2 ^ (64 - cnt) +
          (high / 2 ^ cnt) * (2 ^ cnt * 2 ^ (64 - cnt))) by ring.
  rewrite Z.mod_add by (apply Z.neq_mul_0; split; apply Z.pow_nonzero; lia).
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (Z.mod_pos_bound high (2 ^ cnt)
      ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
    split.
    + apply Z.mul_nonneg_nonneg; lia.
    + apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma u64_join32_range :
  forall low high,
    0 <= low < U64_MOD ->
    0 <= high < U64_MOD ->
    0 <=
      Z.lor (Z.shiftr low 32)
        (unsigned_last_nbits (Z.shiftl high 32) 64) <
      U64_MOD.
Proof.
  intros low high Hlow Hhigh.
  pose proof
    (u64_rshift_lor_add__u256_shift low high 32 Hlow ltac:(lia))
    as Hlor.
  replace (64 - 32) with 32 in Hlor by lia.
  rewrite Hlor.
  pose proof
    (unsigned_last_nbits_shiftl_high__u256_shift high 32 Hhigh
      ltac:(lia))
    as Hshift.
  replace (64 - 32) with 32 in Hshift by lia.
  rewrite Hshift.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound high (2 ^ 32) ltac:(lia)) as Hmod.
  assert (Hdiv : 0 <= low / 2 ^ 32 < 2 ^ 32).
  {
    unfold U64_MOD in Hlow.
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  unfold U64_MOD.
  nia.
Qed.

(** * Equality and comparison *)

Definition u256_limb_diff
    (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  Z.lor (Z.lor (Z.lor (Z.lxor a0 b0) (Z.lxor a1 b1))
               (Z.lxor a2 b2))
        (Z.lxor a3 b3).

Lemma u256_limb_diff_eq_zero_iff__eq :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    u256_limb_diff a0 a1 a2 a3 b0 b1 b2 b3 = 0 <->
    a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intros; unfold u256_limb_diff.
  rewrite !Z.lor_eq_0_iff, !Z.lxor_eq_0_iff; tauto.
Qed.

Definition u256_limb_or (x0 x1 x2 x3 : Z) : Z :=
  Z.lor (Z.lor (Z.lor x0 x1) x2) x3.

Lemma u256_limb_or_eq_zero_iff__eq_zero :
  forall x0 x1 x2 x3,
    u256_limb_or x0 x1 x2 x3 = 0 <->
    x0 = 0 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0.
Proof.
  intros; unfold u256_limb_or.
  rewrite !Z.lor_eq_0_iff; tauto.
Qed.

Lemma u256_of_limbs_eq_zero_iff__eq_zero :
  forall x0 x1 x2 x3,
    0 <= x0 -> 0 <= x1 -> 0 <= x2 -> 0 <= x3 ->
    u256_of_limbs x0 x1 x2 x3 = 0 <->
    x0 = 0 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0.
Proof.
  intros; cbv [u256_of_limbs U64_MOD]; nia.
Qed.

Definition u256_one_diff (x0 x1 x2 x3 : Z) : Z :=
  Z.lor (Z.lor (Z.lor (Z.lxor x0 1) x1) x2) x3.

Lemma u256_one_diff_eq_zero_iff__eq_one :
  forall x0 x1 x2 x3,
    u256_one_diff x0 x1 x2 x3 = 0 <->
    x0 = 1 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0.
Proof.
  intros; unfold u256_one_diff.
  rewrite !Z.lor_eq_0_iff, Z.lxor_eq_0_iff; tauto.
Qed.

Lemma u256_of_limbs_eq_one_iff__eq_one :
  forall x0 x1 x2 x3,
    0 <= x0 -> 0 <= x1 -> 0 <= x2 -> 0 <= x3 ->
    u256_of_limbs x0 x1 x2 x3 = 1 <->
    x0 = 1 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0.
Proof.
  intros; cbv [u256_of_limbs U64_MOD]; nia.
Qed.

Lemma u256_limb0_le__ge :
  forall a0 a1 a2 a3 b0,
    b0 <= a0 ->
    u256_of_limbs b0 a1 a2 a3 <= u256_of_limbs a0 a1 a2 a3.
Proof. intros; unfold u256_of_limbs; lia. Qed.

Lemma u256_limb1_ge__ge :
  forall a0 a1 a2 a3 b0 b1,
    0 <= a0 < U64_MOD -> 0 <= b0 < U64_MOD -> b1 < a1 ->
    u256_of_limbs a0 a1 a2 a3 >= u256_of_limbs b0 b1 a2 a3.
Proof. intros; apply Z.le_ge; unfold u256_of_limbs; nia. Qed.

Lemma u256_limb2_ge__ge :
  forall a0 a1 a2 a3 b0 b1 b2,
    0 <= a0 < U64_MOD -> 0 <= a1 < U64_MOD ->
    0 <= b0 < U64_MOD -> 0 <= b1 < U64_MOD -> b2 < a2 ->
    u256_of_limbs a0 a1 a2 a3 >= u256_of_limbs b0 b1 b2 a3.
Proof. intros; apply Z.le_ge; unfold u256_of_limbs; nia. Qed.

Lemma u256_limb3_ge__ge :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD -> 0 <= a1 < U64_MOD -> 0 <= a2 < U64_MOD ->
    0 <= b0 < U64_MOD -> 0 <= b1 < U64_MOD -> 0 <= b2 < U64_MOD ->
    b3 < a3 ->
    u256_of_limbs a0 a1 a2 a3 >= u256_of_limbs b0 b1 b2 b3.
Proof. intros; apply Z.le_ge; unfold u256_of_limbs; nia. Qed.

(** * Bit and carry arithmetic for [raw_pow] and [raw_mul] *)

Lemma u64_lor_even_bit :
  forall x b : Z,
    (exists k, x = 2 * k) ->
    (b = 0 \/ b = 1) ->
    Z.lor x b = x + b.
Proof.
  intros x b [k Hx] [Hb | Hb]; subst b.
  - rewrite Z.lor_0_r. lia.
  - assert (Hland : Z.land x 1 = 0).
    {
      subst x.
      replace 1 with (Z.ones 1) by reflexivity.
      rewrite Z.land_ones by lia.
      change ((2 * k) mod 2 = 0).
      rewrite Z.mul_comm.
      apply Z_mod_mult.
    }
    pose proof (Z.add_lor_land x 1).
    lia.
Qed.

Lemma u64_shiftr63_bit :
  forall x : Z,
    0 <= x < U64_MOD ->
    Z.shiftr x 63 = 0 \/ Z.shiftr x 63 = 1.
Proof.
  intros x Hx.
  unfold U64_MOD in Hx.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_pos x (2 ^ 63) ltac:(lia) ltac:(lia)) as Hnonneg.
  assert (Hlt : x / 2 ^ 63 < 2).
  {
    apply Z.div_lt_upper_bound; lia.
  }
  lia.
Qed.

Lemma u64_shiftr63_range :
  forall x : Z,
    0 <= x < U64_MOD ->
    0 <= Z.shiftr x 63 <= 1.
Proof.
  intros x Hx.
  destruct (u64_shiftr63_bit x Hx) as [Hbit | Hbit];
    rewrite Hbit; lia.
Qed.

Lemma u64_double_split :
  forall x : Z,
    2 * x =
      unsigned_last_nbits (Z.shiftl x 1) 64 +
      Z.shiftr x 63 * U64_MOD.
Proof.
  intro x.
  unfold unsigned_last_nbits, U64_MOD.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  assert (HB : 2 ^ 64 = 2 * 2 ^ 63) by reflexivity.
  pose proof (Z.div_mod (2 * x) (2 ^ 64) ltac:(lia)) as Hdiv.
  rewrite HB in Hdiv.
  rewrite Z.div_mul_cancel_l in Hdiv by lia.
  rewrite HB.
  replace (x * 2) with (2 * x) by ring.
  nia.
Qed.

Lemma u64_double_low_even :
  forall x : Z,
    exists k : Z,
      unsigned_last_nbits (Z.shiftl x 1) 64 = 2 * k.
Proof.
  intro x.
  pose proof (u64_double_split x) as Hsplit.
  exists (x - Z.shiftr x 63 * 2 ^ 63).
  unfold U64_MOD in Hsplit.
  replace (2 ^ 64) with (2 * 2 ^ 63) in Hsplit by reflexivity.
  nia.
Qed.

Lemma u64_double_u128 :
  forall lo hi : Z,
    0 <= lo < U64_MOD ->
    0 <= hi < U64_MOD ->
    2 * (lo + hi * U64_MOD) =
      unsigned_last_nbits (Z.shiftl lo 1) 64 +
      Z.lor (unsigned_last_nbits (Z.shiftl hi 1) 64)
            (Z.shiftr lo 63) * U64_MOD +
      Z.shiftr hi 63 * U64_MOD * U64_MOD.
Proof.
  intros lo hi Hlo Hhi.
  pose proof (u64_double_split lo) as Hlo_split.
  pose proof (u64_double_split hi) as Hhi_split.
  pose proof (u64_double_low_even hi) as Heven.
  pose proof (u64_shiftr63_bit lo Hlo) as Hbit.
  pose proof
    (u64_lor_even_bit
       (unsigned_last_nbits (Z.shiftl hi 1) 64)
       (Z.shiftr lo 63) Heven Hbit) as Hlor.
  rewrite Hlor.
  nia.
Qed.

Lemma u64_double_lor_range :
  forall hi lo : Z,
    0 <= hi < U64_MOD ->
    0 <= lo < U64_MOD ->
    0 <=
      Z.lor (unsigned_last_nbits (Z.shiftl hi 1) 64)
            (Z.shiftr lo 63) < U64_MOD.
Proof.
  intros hi lo Hhi Hlo.
  pose proof
    (unsigned_Lastnbits_range (Z.shiftl hi 1) 64 ltac:(lia))
    as Hlow_range.
  change
    (0 <= unsigned_last_nbits (Z.shiftl hi 1) 64 < U64_MOD)
    in Hlow_range.
  destruct (u64_double_low_even hi) as [k Heven].
  pose proof (u64_shiftr63_bit lo Hlo) as Hbit.
  pose proof
    (u64_lor_even_bit
       (unsigned_last_nbits (Z.shiftl hi 1) 64)
       (Z.shiftr lo 63) (ex_intro _ k Heven) Hbit) as Hlor.
  rewrite Hlor.
  split.
  - destruct Hbit; lia.
  - unfold U64_MOD in *.
    destruct Hbit; nia.
Qed.

Lemma u8_last_nbits_bits2 :
  forall a b : Z,
    0 <= a <= 1 ->
    0 <= b <= 1 ->
    unsigned_last_nbits (a + b) 8 = a + b.
Proof.
  intros; apply unsigned_last_nbits_eq; lia.
Qed.

Lemma u8_last_nbits_bits3 :
  forall a b c : Z,
    0 <= a <= 1 ->
    0 <= b <= 1 ->
    0 <= c <= 1 ->
    unsigned_last_nbits (a + b + c) 8 = a + b + c.
Proof.
  intros; apply unsigned_last_nbits_eq; lia.
Qed.

Lemma u8_last_nbits_bits4 :
  forall a b c d : Z,
    0 <= a <= 1 ->
    0 <= b <= 1 ->
    0 <= c <= 1 ->
    0 <= d <= 1 ->
    unsigned_last_nbits (a + b + c + d) 8 = a + b + c + d.
Proof.
  intros; apply unsigned_last_nbits_eq; lia.
Qed.

Lemma u8_last_nbits_nested4 :
  forall a b c d : Z,
    0 <= a <= 1 ->
    0 <= b <= 1 ->
    0 <= c <= 1 ->
    0 <= d <= 1 ->
    unsigned_last_nbits
      (unsigned_last_nbits
         (unsigned_last_nbits (a + b) 8 + c) 8 + d) 8 =
      a + b + c + d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  rewrite (u8_last_nbits_bits2 a b Ha Hb).
  rewrite (u8_last_nbits_bits3 a b c Ha Hb Hc).
  apply u8_last_nbits_bits4; assumption.
Qed.

Lemma radix_add2_conservation :
  forall B old0 old1 lo hi new0 new1 carry0 carry1 : Z,
    old0 + lo = new0 + carry0 * B ->
    old1 + hi + carry0 = new1 + carry1 * B ->
    old0 + old1 * B + (lo + hi * B) =
      new0 + new1 * B + carry1 * B * B.
Proof.
  intros B old0 old1 lo hi new0 new1 carry0 carry1 Hlow Hhigh.
  nia.
Qed.

Lemma initial_square_top_carry_zero :
  forall B x lo hi out0 carry0 out1 carry1 : Z,
    1 < B ->
    0 <= x < B ->
    0 <= out0 ->
    0 <= out1 ->
    0 <= carry1 ->
    x * x = lo + hi * B ->
    lo = out0 + carry0 * B ->
    hi + carry0 = out1 + carry1 * B ->
    carry1 = 0.
Proof.
  intros B x lo hi out0 carry0 out1 carry1
    HB Hx Ho0 Ho1 Hc Hmul Hlow Hhigh.
  nia.
Qed.

(** * Montgomery-reduction invariants *)

Definition zero_prefix (i : Z) (xs : list Z) : Prop :=
  forall j, 0 <= j < i -> Znth j xs 0 = 0.

Definition U576_MOD : Z := U64_POW 9.

Lemma zero_prefix_replace_Znth_after :
  forall xs k i v,
    zero_prefix k xs ->
    k <= i ->
    0 <= i < Zlength xs ->
    zero_prefix k (replace_Znth i v xs).
Proof.
  intros xs k i v Hzero Hki Hi.
  unfold zero_prefix in *.
  intros j Hj.
  rewrite Znth_replace_Znth_Diff by lia.
  apply Hzero.
  exact Hj.
Qed.

Lemma zero_prefix_replace_Znth_extend :
  forall xs i,
    zero_prefix i xs ->
    0 <= i < Zlength xs ->
    zero_prefix (i + 1) (replace_Znth i 0 xs).
Proof.
  intros xs i Hzero Hi.
  unfold zero_prefix in *.
  intros j Hj.
  destruct (Z.eq_dec j i) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by exact Hi.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Hzero.
    lia.
Qed.

Lemma sm2_p_shifted_limbs :
  forall factor i,
    0 <= i ->
    factor * SM2_P_Z * U64_POW i =
      factor * SM2_P_LIMB_0 * U64_POW i +
      factor * SM2_P_LIMB_1 * U64_POW (i + 1) +
      factor * SM2_P_LIMB_2 * U64_POW (i + 2) +
      factor * SM2_P_LIMB_3 * U64_POW (i + 3).
Proof.
  intros factor i Hi.
  destruct sm2_p_limbs as [_ [_ [_ [_ HP]]]].
  rewrite HP.
  unfold u256_of_limbs.
  assert (H1 : U64_POW (i + 1) = U64_POW i * U64_MOD)
    by (apply U64_POW_succ; lia).
  assert (H2 : U64_POW (i + 2) = U64_POW i * U64_MOD ^ 2).
  {
    replace (i + 2) with ((i + 1) + 1) by lia.
    rewrite U64_POW_succ by lia.
    rewrite H1.
    ring.
  }
  assert (H3 : U64_POW (i + 3) = U64_POW i * U64_MOD ^ 3).
  {
    replace (i + 3) with ((i + 2) + 1) by lia.
    rewrite U64_POW_succ by lia.
    rewrite H2.
    ring.
  }
  rewrite H1, H2, H3.
  change (U64_MOD ^ i) with (U64_POW i).
  ring.
Qed.

Lemma two_U512_lt_U576 : 2 * U512_MOD < U576_MOD.
Proof. vm_compute. reflexivity. Qed.

Lemma u64_montgomery_coefficient_bound :
  forall K factor i,
    0 <= i ->
    0 <= K < U64_POW i ->
    0 <= factor < U64_MOD ->
    0 <= K + factor * U64_POW i < U64_POW (i + 1).
Proof.
  intros K factor i Hi HK Hfactor.
  exact
    (coefficient_extend_bound
      U64_MOD i K factor
      ltac:(cbv [U64_MOD]; lia)
      Hi HK Hfactor).
Qed.

Lemma sm2p_montgomery_accumulator_bound :
  forall T K factor i,
    0 <= T < U512_MOD ->
    0 <= i < 4 ->
    0 <= K < U64_POW i ->
    0 <= factor < U64_MOD ->
    0 <= T + (K + factor * U64_POW i) * SM2_P_Z < U576_MOD.
Proof.
  intros T K factor i HT Hi HK Hfactor.
  pose proof
    (u64_montgomery_coefficient_bound
      K factor i (proj1 Hi) HK Hfactor)
    as Hcoef.
  destruct sm2_p_montgomery_bounds as [HP _].
  assert (Hpow_le : U64_POW (i + 1) <= U64_POW 4).
  {
    unfold U64_POW.
    apply Z.pow_le_mono_r.
    - unfold U64_MOD. lia.
    - lia.
  }
  rewrite <- U256_MOD_as_U64_POW_4 in Hpow_le.
  assert (Hprod :
    0 <= (K + factor * U64_POW i) * SM2_P_Z < U512_MOD).
  {
    unfold U512_MOD.
    nia.
  }
  pose proof two_U512_lt_U576.
  nia.
Qed.

Lemma sm2p_montgomery_stage1_bound :
  forall T K factor i,
    0 <= T < U512_MOD ->
    0 <= i < 4 ->
    0 <= K < U64_POW i ->
    0 <= factor < U64_MOD ->
    0 <= T + K * SM2_P_Z +
      factor * SM2_P_LIMB_0 * U64_POW i < U576_MOD.
Proof.
  intros T K factor i HT Hi HK Hfactor.
  pose proof
    (sm2p_montgomery_accumulator_bound T K factor i HT Hi HK Hfactor)
    as Hfull.
  pose proof (sm2_p_shifted_limbs factor i (proj1 Hi)) as Hshift.
  destruct sm2_p_limbs as
    [HL0 [HL1 [HL2 [HL3 _]]]].
  pose proof (U64_POW_nonneg i) as HP0.
  pose proof (U64_POW_nonneg (i + 1)) as HP1.
  pose proof (U64_POW_nonneg (i + 2)) as HP2.
  pose proof (U64_POW_nonneg (i + 3)) as HP3.
  destruct sm2_p_montgomery_bounds as [Hprime _].
  nia.
Qed.

Lemma sm2p_montgomery_stage2_bound :
  forall T K factor i,
    0 <= T < U512_MOD ->
    0 <= i < 4 ->
    0 <= K < U64_POW i ->
    0 <= factor < U64_MOD ->
    0 <= T + K * SM2_P_Z +
      factor * SM2_P_LIMB_0 * U64_POW i +
      factor * SM2_P_LIMB_1 * U64_POW (i + 1) < U576_MOD.
Proof.
  intros T K factor i HT Hi HK Hfactor.
  pose proof
    (sm2p_montgomery_accumulator_bound T K factor i HT Hi HK Hfactor)
    as Hfull.
  pose proof (sm2_p_shifted_limbs factor i (proj1 Hi)) as Hshift.
  destruct sm2_p_limbs as
    [HL0 [HL1 [HL2 [HL3 _]]]].
  pose proof (U64_POW_nonneg i) as HP0.
  pose proof (U64_POW_nonneg (i + 1)) as HP1.
  pose proof (U64_POW_nonneg (i + 2)) as HP2.
  pose proof (U64_POW_nonneg (i + 3)) as HP3.
  destruct sm2_p_montgomery_bounds as [Hprime _].
  nia.
Qed.

Lemma sm2p_montgomery_stage3_bound :
  forall T K factor i,
    0 <= T < U512_MOD ->
    0 <= i < 4 ->
    0 <= K < U64_POW i ->
    0 <= factor < U64_MOD ->
    0 <= T + K * SM2_P_Z +
      factor * SM2_P_LIMB_0 * U64_POW i +
      factor * SM2_P_LIMB_1 * U64_POW (i + 1) +
      factor * SM2_P_LIMB_2 * U64_POW (i + 2) < U576_MOD.
Proof.
  intros T K factor i HT Hi HK Hfactor.
  pose proof
    (sm2p_montgomery_accumulator_bound T K factor i HT Hi HK Hfactor)
    as Hfull.
  pose proof (sm2_p_shifted_limbs factor i (proj1 Hi)) as Hshift.
  destruct sm2_p_limbs as
    [HL0 [HL1 [HL2 [HL3 _]]]].
  pose proof (U64_POW_nonneg i) as HP0.
  pose proof (U64_POW_nonneg (i + 1)) as HP1.
  pose proof (U64_POW_nonneg (i + 2)) as HP2.
  pose proof (U64_POW_nonneg (i + 3)) as HP3.
  destruct sm2_p_montgomery_bounds as [Hprime _].
  nia.
Qed.
Definition u512_of_limbs
  (x0 x1 x2 x3 x4 x5 x6 x7 : Z) : Z :=
  x0 + x1 * U64_MOD + x2 * U64_MOD ^ 2 + x3 * U64_MOD ^ 3 +
  x4 * U64_MOD ^ 4 + x5 * U64_MOD ^ 5 +
  x6 * U64_MOD ^ 6 + x7 * U64_MOD ^ 7.

Definition u576_of_limbs
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Z) : Z :=
  u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 +
  x8 * U64_MOD ^ 8.

Definition sm2n_mont_red_spec (t r : Z) : Prop :=
  0 <= t < SM2_N_Z * U256_MOD /\
  0 <= r < SM2_N_Z /\
  (r * U256_MOD - t) mod SM2_N_Z = 0.

Definition sm2n_mont_mul_spec (x y r : Z) : Prop :=
  0 <= x < SM2_N_Z /\
  0 <= y < SM2_N_Z /\
  sm2n_mont_red_spec (x * y) r.

Definition raw_mul_spec (a b lo hi : Z) : Prop :=
  0 <= lo < U256_MOD /\
  0 <= hi < U256_MOD /\
  a * b = lo + hi * U256_MOD.

Definition u64_zeros (n : Z) : list Z :=
  repeat 0%Z (Z.to_nat n).

Definition raw_mul_locals_ok
  (h l carry carry2 i j k start finish : Z) : Prop :=
  0 <= h < U64_MOD /\
  0 <= l < U64_MOD /\
  0 <= carry <= 1 /\
  0 <= carry2 < U64_MOD /\
  0 <= i <= 8 /\
  0 <= j <= 8 /\
  0 <= k <= 8 /\
  0 <= start <= 4 /\
  0 <= finish <= 4.

Definition raw_mul_zero_inv (i : Z) (rs : list Z) : Prop :=
  0 <= i <= 8 /\
  Zlength rs = i /\
  u64_list_bounded rs /\
  rs = u64_zeros i.

Definition raw_mul_outer_inv
  (av bv : list Z) (k : Z) (rs : list Z) : Prop :=
  0 <= k <= 7 /\
  Zlength av = 4 /\
  Zlength bv = 4 /\
  Zlength rs = 8 /\
  u64_list_bounded av /\
  u64_list_bounded bv /\
  u64_list_bounded rs /\
  (k = 0 -> u64_list_value rs = 0) /\
  (k = 7 ->
    raw_mul_spec
      (u64_list_value av)
      (u64_list_value bv)
      (u64_list_value (sublist 0 4 rs))
      (u64_list_value (sublist 4 8 rs))).

Definition raw_mul_inner_inv
  (av bv : list Z) (k start finish i carry2 : Z) (rs : list Z) : Prop :=
  0 <= k < 7 /\
  0 <= start /\
  start <= i /\
  i <= finish + 1 /\
  finish < 4 /\
  0 <= carry2 < U64_MOD /\
  Zlength av = 4 /\
  Zlength bv = 4 /\
  Zlength rs = 8 /\
  u64_list_bounded av /\
  u64_list_bounded bv /\
  u64_list_bounded rs.

Definition sm2n_core_locals_ok
  (carry h l factor i j k : Z) : Prop :=
  0 <= carry <= 1 /\
  0 <= h < U64_MOD /\
  0 <= l < U64_MOD /\
  0 <= factor < U64_MOD /\
  0 <= i <= 4 /\
  0 <= j <= 4 /\
  0 <= k <= 9.

Definition sm2n_red_stage (completed t v : Z) : Prop :=
  0 <= completed <= 4 /\
  0 <= t < SM2_N_Z * U256_MOD /\
  exists coefficient,
    0 <= coefficient < U64_POW completed /\
    v = t + coefficient * SM2_N_Z /\
    v mod U64_POW completed = 0.

Definition sm2n_red_stage_1 (t v : Z) : Prop :=
  sm2n_red_stage 1 t v.

Definition sm2n_red_stage_2 (t v : Z) : Prop :=
  sm2n_red_stage 2 t v.

Definition sm2n_red_stage_3 (t v : Z) : Prop :=
  sm2n_red_stage 3 t v.

Definition sm2n_red_stage_4 (t v : Z) : Prop :=
  sm2n_red_stage 4 t v.

Lemma sm2n_montgomery_radix :
  U64_POW 4 = U256_MOD.
Proof. vm_compute. reflexivity. Qed.

Lemma sm2n_montgomery_parameters_valid :
  0 < SM2_N_Z < U256_MOD /\
  Z.gcd SM2_N_Z U256_MOD = 1.
Proof.
  split.
  - exact sm2_n_bounds.
  - vm_compute.
    reflexivity.
Qed.

Lemma sm2n_word_negative_inverse :
  0 <= SM2_NEG_INV_N < U64_MOD /\
  exists quotient,
    SM2_N0_Z * SM2_NEG_INV_N + 1 = quotient * U64_MOD.
Proof.
  split.
  - split.
    + cbv [SM2_NEG_INV_N].
      lia.
    + cbv [SM2_NEG_INV_N U64_MOD].
      lia.
  - exists SM2_NEG_INV_N_QUOTIENT.
    exact sm2_neg_inv_n0_multiple.
Qed.

Lemma sm2n_red_stage_input_bound :
  forall completed t v,
    sm2n_red_stage completed t v ->
    0 <= t < SM2_N_Z * U256_MOD.
Proof.
  intros completed t v Hstage.
  unfold sm2n_red_stage in Hstage.
  tauto.
Qed.

Definition sm2n_red_outer_inv (t i : Z) (ts : list Z) : Prop :=
  0 <= i <= 4 /\
  0 <= t < SM2_N_Z * U256_MOD /\
  Zlength ts = 9 /\
  u64_list_bounded ts /\
  (i = 0 -> u64_list_value ts = t) /\
  (i = 1 -> sm2n_red_stage_1 t (u64_list_value ts)) /\
  (i = 2 -> sm2n_red_stage_2 t (u64_list_value ts)) /\
  (i = 3 -> sm2n_red_stage_3 t (u64_list_value ts)) /\
  (i = 4 -> sm2n_red_stage_4 t (u64_list_value ts)).

Definition sm2n_red_inner_inv
  (t i j factor : Z) (ts : list Z) : Prop :=
  0 <= i < 4 /\
  0 <= j <= 4 /\
  0 <= factor < U64_MOD /\
  0 <= t < SM2_N_Z * U256_MOD /\
  Zlength ts = 9 /\
  u64_list_bounded ts.

Definition sm2n_red_carry_inv
  (t i j factor k carry : Z) (ts : list Z) : Prop :=
  0 <= i < 4 /\
  0 <= j < 4 /\
  i + j + 2 <= k <= 9 /\
  0 <= carry <= 1 /\
  0 <= factor < U64_MOD /\
  0 <= t < SM2_N_Z * U256_MOD /\
  Zlength ts = 9 /\
  u64_list_bounded ts.

Definition sm2n_copy_inv (ts : list Z) (i : Z) (rs : list Z) : Prop :=
  0 <= i <= 4 /\
  Zlength ts = 9 /\
  Zlength rs = 4 /\
  u64_list_bounded ts /\
  u64_list_bounded rs /\
  forall k, 0 <= k < i -> Znth k rs 0 = Znth (k + 4) ts 0.

Definition raw_mul_prefix_0
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  a0 * b0.

Definition raw_mul_prefix_1
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  raw_mul_prefix_0 a0 a1 a2 a3 b0 b1 b2 b3 +
  (a0 * b1 + a1 * b0) * U64_MOD.

Definition raw_mul_prefix_2
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  raw_mul_prefix_1 a0 a1 a2 a3 b0 b1 b2 b3 +
  (a0 * b2 + a1 * b1 + a2 * b0) * U64_MOD ^ 2.

Definition raw_mul_prefix_3
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  raw_mul_prefix_2 a0 a1 a2 a3 b0 b1 b2 b3 +
  (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * U64_MOD ^ 3.

Definition raw_mul_prefix_4
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  raw_mul_prefix_3 a0 a1 a2 a3 b0 b1 b2 b3 +
  (a1 * b3 + a2 * b2 + a3 * b1) * U64_MOD ^ 4.

Definition raw_mul_prefix_5
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  raw_mul_prefix_4 a0 a1 a2 a3 b0 b1 b2 b3 +
  (a2 * b3 + a3 * b2) * U64_MOD ^ 5.

Definition raw_mul_prefix_6
  (a0 a1 a2 a3 b0 b1 b2 b3 : Z) : Z :=
  raw_mul_prefix_5 a0 a1 a2 a3 b0 b1 b2 b3 +
  (a3 * b3) * U64_MOD ^ 6.

Lemma raw_mul_prefix_3_to_6_conservation :
  forall
    a0 a1 a2 a3 b0 b1 b2 b3
    r0 r1 r2 r3 r4 r5
    d4a d5a c13 d4b d5b c22 r4f d5c c31
    d5d d6a c23 r5f d6b c32 r6f r7f c33,
    raw_mul_prefix_3 a0 a1 a2 a3 b0 b1 b2 b3 =
      r0 + r1 * U64_MOD + r2 * U64_MOD ^ 2 +
      r3 * U64_MOD ^ 3 + r4 * U64_MOD ^ 4 + r5 * U64_MOD ^ 5 ->
    r4 + r5 * U64_MOD + a1 * b3 =
      d4a + d5a * U64_MOD + c13 * U64_MOD ^ 2 ->
    d4a + d5a * U64_MOD + a2 * b2 =
      d4b + d5b * U64_MOD + c22 * U64_MOD ^ 2 ->
    d4b + d5b * U64_MOD + a3 * b1 =
      r4f + d5c * U64_MOD + c31 * U64_MOD ^ 2 ->
    d5c + (c13 + c22 + c31) * U64_MOD + a2 * b3 =
      d5d + d6a * U64_MOD + c23 * U64_MOD ^ 2 ->
    d5d + d6a * U64_MOD + a3 * b2 =
      r5f + d6b * U64_MOD + c32 * U64_MOD ^ 2 ->
    d6b + (c23 + c32) * U64_MOD + a3 * b3 =
      r6f + r7f * U64_MOD + c33 * U64_MOD ^ 2 ->
    raw_mul_prefix_6 a0 a1 a2 a3 b0 b1 b2 b3 =
      u512_of_limbs r0 r1 r2 r3 r4f r5f r6f r7f +
      c33 * U64_MOD ^ 8.
Proof.
  intros.
  unfold raw_mul_prefix_6, raw_mul_prefix_5, raw_mul_prefix_4,
         u512_of_limbs.
  rewrite H.
  cbv [U64_MOD] in *.
  ring_simplify in H0.
  ring_simplify in H1.
  ring_simplify in H2.
  ring_simplify in H3.
  ring_simplify in H4.
  ring_simplify in H5.
  ring_simplify.
  lia.
Qed.

Lemma u64_mul_range :
  forall x y,
    0 <= x < U64_MOD ->
    0 <= y < U64_MOD ->
    0 <= x * y < U64_MOD ^ 2.
Proof.
  intros x y Hx Hy.
  change (0 <= x * y < limb_radix U64_MOD 2).
  apply limb_digit_product_range; try assumption.
  cbv [U64_MOD].
  lia.
Qed.

Lemma raw_mul_prefix_0_bound :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= raw_mul_prefix_0 a0 a1 a2 a3 b0 b1 b2 b3 < U64_MOD ^ 3.
Proof.
  intros.
  pose proof (u64_mul_range a0 b0 H H0).
  unfold raw_mul_prefix_0 in *.
  assert (1 < U64_MOD) by (cbv [U64_MOD]; lia).
  nia.
Qed.

Lemma raw_mul_prefix_1_bound :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= a1 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= b1 < U64_MOD ->
    0 <= raw_mul_prefix_1 a0 a1 a2 a3 b0 b1 b2 b3 < U64_MOD ^ 4.
Proof.
  intros.
  set (p00 := a0 * b0).
  set (p01 := a0 * b1).
  set (p10 := a1 * b0).
  assert (Hp00 : 0 <= p00 < U64_MOD ^ 2)
    by (subst p00; apply u64_mul_range; assumption).
  assert (Hp01 : 0 <= p01 < U64_MOD ^ 2)
    by (subst p01; apply u64_mul_range; assumption).
  assert (Hp10 : 0 <= p10 < U64_MOD ^ 2)
    by (subst p10; apply u64_mul_range; assumption).
  unfold raw_mul_prefix_1, raw_mul_prefix_0.
  fold p00 p01 p10.
  cbv [U64_MOD] in *.
  lia.
Qed.

Lemma raw_mul_prefix_2_bound :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= a1 < U64_MOD ->
    0 <= a2 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= b1 < U64_MOD ->
    0 <= b2 < U64_MOD ->
    0 <= raw_mul_prefix_2 a0 a1 a2 a3 b0 b1 b2 b3 < U64_MOD ^ 5.
Proof.
  intros.
  set (p00 := a0 * b0).
  set (p01 := a0 * b1).
  set (p10 := a1 * b0).
  set (p02 := a0 * b2).
  set (p11 := a1 * b1).
  set (p20 := a2 * b0).
  assert (Hp00 : 0 <= p00 < U64_MOD ^ 2)
    by (subst p00; apply u64_mul_range; assumption).
  assert (Hp01 : 0 <= p01 < U64_MOD ^ 2)
    by (subst p01; apply u64_mul_range; assumption).
  assert (Hp10 : 0 <= p10 < U64_MOD ^ 2)
    by (subst p10; apply u64_mul_range; assumption).
  assert (Hp02 : 0 <= p02 < U64_MOD ^ 2)
    by (subst p02; apply u64_mul_range; assumption).
  assert (Hp11 : 0 <= p11 < U64_MOD ^ 2)
    by (subst p11; apply u64_mul_range; assumption).
  assert (Hp20 : 0 <= p20 < U64_MOD ^ 2)
    by (subst p20; apply u64_mul_range; assumption).
  unfold raw_mul_prefix_2, raw_mul_prefix_1, raw_mul_prefix_0.
  fold p00 p01 p10 p02 p11 p20.
  cbv [U64_MOD] in *.
  lia.
Qed.

Lemma raw_mul_prefix_3_bound :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= a1 < U64_MOD ->
    0 <= a2 < U64_MOD ->
    0 <= a3 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= b1 < U64_MOD ->
    0 <= b2 < U64_MOD ->
    0 <= b3 < U64_MOD ->
    0 <= raw_mul_prefix_3 a0 a1 a2 a3 b0 b1 b2 b3 < U64_MOD ^ 6.
Proof.
  intros.
  set (p00 := a0 * b0).
  set (p01 := a0 * b1).
  set (p10 := a1 * b0).
  set (p02 := a0 * b2).
  set (p11 := a1 * b1).
  set (p20 := a2 * b0).
  set (p03 := a0 * b3).
  set (p12 := a1 * b2).
  set (p21 := a2 * b1).
  set (p30 := a3 * b0).
  assert (Hp00 : 0 <= p00 < U64_MOD ^ 2)
    by (subst p00; apply u64_mul_range; assumption).
  assert (Hp01 : 0 <= p01 < U64_MOD ^ 2)
    by (subst p01; apply u64_mul_range; assumption).
  assert (Hp10 : 0 <= p10 < U64_MOD ^ 2)
    by (subst p10; apply u64_mul_range; assumption).
  assert (Hp02 : 0 <= p02 < U64_MOD ^ 2)
    by (subst p02; apply u64_mul_range; assumption).
  assert (Hp11 : 0 <= p11 < U64_MOD ^ 2)
    by (subst p11; apply u64_mul_range; assumption).
  assert (Hp20 : 0 <= p20 < U64_MOD ^ 2)
    by (subst p20; apply u64_mul_range; assumption).
  assert (Hp03 : 0 <= p03 < U64_MOD ^ 2)
    by (subst p03; apply u64_mul_range; assumption).
  assert (Hp12 : 0 <= p12 < U64_MOD ^ 2)
    by (subst p12; apply u64_mul_range; assumption).
  assert (Hp21 : 0 <= p21 < U64_MOD ^ 2)
    by (subst p21; apply u64_mul_range; assumption).
  assert (Hp30 : 0 <= p30 < U64_MOD ^ 2)
    by (subst p30; apply u64_mul_range; assumption).
  unfold raw_mul_prefix_3, raw_mul_prefix_2, raw_mul_prefix_1,
         raw_mul_prefix_0.
  fold p00 p01 p10 p02 p11 p20 p03 p12 p21 p30.
  cbv [U64_MOD] in *.
  lia.
Qed.

Lemma raw_mul_prefix_4_bound :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= a1 < U64_MOD ->
    0 <= a2 < U64_MOD ->
    0 <= a3 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= b1 < U64_MOD ->
    0 <= b2 < U64_MOD ->
    0 <= b3 < U64_MOD ->
    0 <= raw_mul_prefix_4 a0 a1 a2 a3 b0 b1 b2 b3 < U64_MOD ^ 7.
Proof.
  intros.
  set (p13 := a1 * b3).
  set (p22 := a2 * b2).
  set (p31 := a3 * b1).
  pose proof (raw_mul_prefix_3_bound a0 a1 a2 a3 b0 b1 b2 b3
    H H0 H1 H2 H3 H4 H5 H6).
  assert (Hp13 : 0 <= p13 < U64_MOD ^ 2)
    by (subst p13; apply u64_mul_range; assumption).
  assert (Hp22 : 0 <= p22 < U64_MOD ^ 2)
    by (subst p22; apply u64_mul_range; assumption).
  assert (Hp31 : 0 <= p31 < U64_MOD ^ 2)
    by (subst p31; apply u64_mul_range; assumption).
  unfold raw_mul_prefix_4.
  fold p13 p22 p31.
  cbv [U64_MOD] in *.
  lia.
Qed.

Lemma raw_mul_prefix_6_product :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    raw_mul_prefix_6 a0 a1 a2 a3 b0 b1 b2 b3 =
    u256_of_limbs a0 a1 a2 a3 * u256_of_limbs b0 b1 b2 b3.
Proof.
  intros.
  unfold raw_mul_prefix_6, raw_mul_prefix_5, raw_mul_prefix_4,
         raw_mul_prefix_3, raw_mul_prefix_2, raw_mul_prefix_1,
         raw_mul_prefix_0, u256_of_limbs.
  ring.
Qed.

Lemma raw_mul_prefix_6_bound :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= a1 < U64_MOD ->
    0 <= a2 < U64_MOD ->
    0 <= a3 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= b1 < U64_MOD ->
    0 <= b2 < U64_MOD ->
    0 <= b3 < U64_MOD ->
    0 <= raw_mul_prefix_6 a0 a1 a2 a3 b0 b1 b2 b3 < U512_MOD.
Proof.
  intros.
  rewrite raw_mul_prefix_6_product.
  assert (HA : 0 <= u256_of_limbs a0 a1 a2 a3 < U256_MOD)
    by (cbv [u256_of_limbs U64_MOD U256_MOD] in *; lia).
  assert (HB : 0 <= u256_of_limbs b0 b1 b2 b3 < U256_MOD)
    by (cbv [u256_of_limbs U64_MOD U256_MOD] in *; lia).
  replace U512_MOD with (U256_MOD * U256_MOD)
    by (cbv [U512_MOD U256_MOD]; reflexivity).
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - apply Z.mul_lt_mono_nonneg; lia.
Qed.

Lemma u512_as_u256_pair :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 =
    u256_of_limbs x0 x1 x2 x3 +
    u256_of_limbs x4 x5 x6 x7 * U256_MOD.
Proof.
  intros.
  cbv [u512_of_limbs u256_of_limbs U256_MOD U64_MOD].
  ring.
Qed.

Lemma u512_limb3_zero_under_3 :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 < U64_MOD ^ 3 ->
    x3 = 0.
Proof.
  intros.
  cbv [u512_of_limbs U64_MOD] in *.
  lia.
Qed.

Lemma u512_limb4_zero_under_4 :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 < U64_MOD ^ 4 ->
    x4 = 0.
Proof.
  intros.
  cbv [u512_of_limbs U64_MOD] in *.
  lia.
Qed.

Lemma u512_limb5_zero_under_5 :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 < U64_MOD ^ 5 ->
    x5 = 0.
Proof.
  intros.
  cbv [u512_of_limbs U64_MOD] in *.
  lia.
Qed.

Lemma u512_limb6_zero_under_6 :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 < U64_MOD ^ 6 ->
    x6 = 0.
Proof.
  intros.
  cbv [u512_of_limbs U64_MOD] in *.
  lia.
Qed.

Lemma u512_limb7_zero_under_7 :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 < U64_MOD ^ 7 ->
    x7 = 0.
Proof.
  intros.
  cbv [u512_of_limbs U64_MOD] in *.
  lia.
Qed.

Definition mulx32_lo (x : Z) : Z := unsigned_last_nbits x 32.
Definition mulx32_hi (x : Z) : Z := Z.shiftr x 32.

Definition mulx_p0 (a b : Z) : Z :=
  unsigned_last_nbits (mulx32_lo a * mulx32_lo b) 64.

Definition mulx_p1 (a b : Z) : Z :=
  unsigned_last_nbits (mulx32_lo a * unsigned_last_nbits (mulx32_hi b) 32) 64.

Definition mulx_p2 (a b : Z) : Z :=
  unsigned_last_nbits (unsigned_last_nbits (mulx32_hi a) 32 * mulx32_lo b) 64.

Definition mulx_p3 (a b : Z) : Z :=
  unsigned_last_nbits
    (unsigned_last_nbits (mulx32_hi a) 32 *
     unsigned_last_nbits (mulx32_hi b) 32) 64.

Definition mulx_mid (a b : Z) : Z :=
  unsigned_last_nbits (mulx_p1 a b + mulx_p2 a b) 64.

Definition mulx_mid_lo (a b : Z) : Z :=
  unsigned_last_nbits (Z.shiftl (mulx_mid a b) 32) 64.

Definition mulx_mid_hi (a b mid_carry : Z) : Z :=
  unsigned_last_nbits
    (Z.shiftr (mulx_mid a b) 32 + Z.shiftl mid_carry 32) 64.

Definition mulx_lo (a b : Z) : Z :=
  unsigned_last_nbits (mulx_p0 a b + mulx_mid_lo a b) 64.

Definition mulx_hi (a b mid_carry lo_carry : Z) : Z :=
  unsigned_last_nbits
    (mulx_p3 a b +
     unsigned_last_nbits (mulx_mid_hi a b mid_carry + lo_carry) 64) 64.

Lemma mulx_partial_products_frontend :
  forall a b,
    mulx_p0 a b =
      unsigned_last_nbits a 32 * unsigned_last_nbits b 32 /\
    mulx_p1 a b =
      unsigned_last_nbits a 32 *
        unsigned_last_nbits (Z.shiftr b 32) 32 /\
    mulx_p2 a b =
      unsigned_last_nbits (Z.shiftr a 32) 32 *
        unsigned_last_nbits b 32 /\
    mulx_p3 a b =
      unsigned_last_nbits (Z.shiftr a 32) 32 *
        unsigned_last_nbits (Z.shiftr b 32) 32.
Proof.
  intros a b.
  pose proof (unsigned_Lastnbits_range a 32 ltac:(lia)) as Ha_lo.
  pose proof
    (unsigned_Lastnbits_range (Z.shiftr a 32) 32 ltac:(lia)) as Ha_hi.
  pose proof (unsigned_Lastnbits_range b 32 ltac:(lia)) as Hb_lo.
  pose proof
    (unsigned_Lastnbits_range (Z.shiftr b 32) 32 ltac:(lia)) as Hb_hi.
  unfold mulx_p0, mulx_p1, mulx_p2, mulx_p3,
    mulx32_lo, mulx32_hi.
  repeat split; apply unsigned_last_nbits_eq; nia.
Qed.

Lemma u512_of_limbs_range :
  forall x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    0 <= u512_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 < U512_MOD.
Proof.
  intros.
  cbv [u512_of_limbs U64_MOD U256_MOD U512_MOD] in *.
  lia.
Qed.

Lemma u64_add_low_wrap :
  forall x y,
    0 <= x -> x < U64_MOD ->
    0 <= y -> y < U64_MOD ->
    unsigned_last_nbits (x + y) 64 < x ->
    x + y = unsigned_last_nbits (x + y) 64 + U64_MOD.
Proof.
  intros x y Hx0 HxM Hy0 HyM Hlt.
  unfold U64_MOD in *.
  destruct (Z_lt_ge_dec (x + y) (2 ^ 64)) as [Hsmall | Hlarge].
  - rewrite unsigned_last_nbits_eq in Hlt by lia.
    lia.
  - assert (Hmod :
        unsigned_last_nbits (x + y) 64 = x + y - 2 ^ 64).
    {
      unfold unsigned_last_nbits.
      symmetry.
      apply Z.mod_unique with (q := 1); lia.
    }
    rewrite Hmod.
    lia.
Qed.

Lemma u64_add_low_no_wrap :
  forall x y,
    0 <= x -> x < U64_MOD ->
    0 <= y -> y < U64_MOD ->
    unsigned_last_nbits (x + y) 64 >= x ->
    x + y = unsigned_last_nbits (x + y) 64.
Proof.
  intros x y Hx0 HxM Hy0 HyM Hge.
  unfold U64_MOD in *.
  destruct (Z_lt_ge_dec (x + y) (2 ^ 64)) as [Hsmall | Hlarge].
  - rewrite unsigned_last_nbits_eq by lia.
    reflexivity.
  - assert (Hmod :
        unsigned_last_nbits (x + y) 64 = x + y - 2 ^ 64).
    {
      unfold unsigned_last_nbits.
      symmetry.
      apply Z.mod_unique with (q := 1); lia.
    }
    rewrite Hmod in Hge.
    lia.
Qed.

Lemma shiftr32_range_u64 :
  forall x, 0 <= x < U64_MOD -> 0 <= Z.shiftr x 32 < U32_MOD.
Proof.
  intros x Hx.
  unfold U64_MOD, U32_MOD in *.
  rewrite Z.shiftr_div_pow2 by lia.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma u64_split_32 :
  forall x,
    0 <= x < U64_MOD ->
    x = mulx32_lo x + mulx32_hi x * U32_MOD /\
    0 <= mulx32_lo x < U32_MOD /\
    0 <= mulx32_hi x < U32_MOD.
Proof.
  intros x Hx.
  unfold mulx32_lo, mulx32_hi, U32_MOD.
  assert (Hmod : unsigned_last_nbits x 32 = x mod 2 ^ 32).
  {
    unfold unsigned_last_nbits.
    reflexivity.
  }
  assert (Hdiv : Z.shiftr x 32 = x / 2 ^ 32).
  {
    rewrite Z.shiftr_div_pow2 by lia.
    reflexivity.
  }
  rewrite Hmod, Hdiv.
  pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)) as Hdm.
  split; [lia |].
  split.
  - apply Z.mod_pos_bound; lia.
  - unfold U64_MOD in Hx.
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

Lemma u256_split_u32_limbs :
  forall x0 x1 x2 x3,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= unsigned_last_nbits x0 32 < U32_MOD /\
    0 <= unsigned_last_nbits (Z.shiftr x0 32) 32 < U32_MOD /\
    0 <= unsigned_last_nbits x1 32 < U32_MOD /\
    0 <= unsigned_last_nbits (Z.shiftr x1 32) 32 < U32_MOD /\
    0 <= unsigned_last_nbits x2 32 < U32_MOD /\
    0 <= unsigned_last_nbits (Z.shiftr x2 32) 32 < U32_MOD /\
    0 <= unsigned_last_nbits x3 32 < U32_MOD /\
    0 <= unsigned_last_nbits (Z.shiftr x3 32) 32 < U32_MOD /\
    u256_of_limbs x0 x1 x2 x3 =
      unsigned_last_nbits x0 32 +
        unsigned_last_nbits (Z.shiftr x0 32) 32 * U32_MOD +
      (unsigned_last_nbits x1 32 +
        unsigned_last_nbits (Z.shiftr x1 32) 32 * U32_MOD) * U64_MOD +
      (unsigned_last_nbits x2 32 +
        unsigned_last_nbits (Z.shiftr x2 32) 32 * U32_MOD) *
        U64_MOD * U64_MOD +
      (unsigned_last_nbits x3 32 +
        unsigned_last_nbits (Z.shiftr x3 32) 32 * U32_MOD) *
        U64_MOD * U64_MOD * U64_MOD.
Proof.
  intros x0 x1 x2 x3 Hx0 Hx1 Hx2 Hx3.
  pose proof (u64_split_32 x0 Hx0) as Hsplit0.
  pose proof (u64_split_32 x1 Hx1) as Hsplit1.
  pose proof (u64_split_32 x2 Hx2) as Hsplit2.
  pose proof (u64_split_32 x3 Hx3) as Hsplit3.
  unfold mulx32_lo, mulx32_hi in Hsplit0, Hsplit1, Hsplit2, Hsplit3.
  destruct Hsplit0 as [Heq0 [Hlo0 Hhi0]].
  destruct Hsplit1 as [Heq1 [Hlo1 Hhi1]].
  destruct Hsplit2 as [Heq2 [Hlo2 Hhi2]].
  destruct Hsplit3 as [Heq3 [Hlo3 Hhi3]].
  assert (Hcast0 :
    unsigned_last_nbits (Z.shiftr x0 32) 32 = Z.shiftr x0 32).
  {
    apply unsigned_last_nbits_eq.
    unfold U32_MOD in Hhi0.
    exact Hhi0.
  }
  assert (Hcast1 :
    unsigned_last_nbits (Z.shiftr x1 32) 32 = Z.shiftr x1 32).
  {
    apply unsigned_last_nbits_eq.
    unfold U32_MOD in Hhi1.
    exact Hhi1.
  }
  assert (Hcast2 :
    unsigned_last_nbits (Z.shiftr x2 32) 32 = Z.shiftr x2 32).
  {
    apply unsigned_last_nbits_eq.
    unfold U32_MOD in Hhi2.
    exact Hhi2.
  }
  assert (Hcast3 :
    unsigned_last_nbits (Z.shiftr x3 32) 32 = Z.shiftr x3 32).
  {
    apply unsigned_last_nbits_eq.
    unfold U32_MOD in Hhi3.
    exact Hhi3.
  }
  rewrite Hcast0, Hcast1, Hcast2, Hcast3.
  repeat split; try assumption;
    cbv [u256_of_limbs U64_MOD U32_MOD] in *; lia.
Qed.

Lemma mulx_u64_correct :
  forall a b mid_carry lo_carry,
    0 <= a < U64_MOD ->
    0 <= b < U64_MOD ->
    (mid_carry = 1 /\ mulx_mid a b < mulx_p1 a b \/
     mid_carry = 0 /\ mulx_mid a b >= mulx_p1 a b) ->
    (lo_carry = 1 /\ mulx_lo a b < mulx_mid_lo a b \/
     lo_carry = 0 /\ mulx_lo a b >= mulx_mid_lo a b) ->
    0 <= mulx_lo a b < U64_MOD /\
    0 <= mulx_hi a b mid_carry lo_carry < U64_MOD /\
    a * b = mulx_lo a b + mulx_hi a b mid_carry lo_carry * U64_MOD.
Proof.
  intros a b mid_carry lo_carry Ha Hb Hmidcase Hlocase.
  pose proof (u64_split_32 a Ha) as [Ha_split [Ha0 Ha1]].
  pose proof (u64_split_32 b Hb) as [Hb_split [Hb0 Hb1]].
  set (alo := mulx32_lo a) in *.
  set (ahi := mulx32_hi a) in *.
  set (blo := mulx32_lo b) in *.
  set (bhi := mulx32_hi b) in *.
  assert (Hp0small : 0 <= alo * blo < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; nia. }
  assert (Hp1small : 0 <= alo * bhi < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; nia. }
  assert (Hp2small : 0 <= ahi * blo < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; nia. }
  assert (Hp3small : 0 <= ahi * bhi < U64_MOD).
  { unfold U32_MOD, U64_MOD in *; nia. }
  assert (Hp0 : mulx_p0 a b = alo * blo).
  {
    unfold mulx_p0, mulx32_lo.
    fold alo blo.
    rewrite unsigned_last_nbits_eq; [reflexivity | exact Hp0small].
  }
  assert (Hp1 : mulx_p1 a b = alo * bhi).
  {
    unfold mulx_p1.
    change (unsigned_last_nbits (alo * unsigned_last_nbits bhi 32) 64 =
            alo * bhi).
    replace (unsigned_last_nbits bhi 32) with bhi
      by (symmetry; apply unsigned_last_nbits_eq; exact Hb1).
    rewrite unsigned_last_nbits_eq; [reflexivity | exact Hp1small].
  }
  assert (Hp2 : mulx_p2 a b = ahi * blo).
  {
    unfold mulx_p2.
    change (unsigned_last_nbits (unsigned_last_nbits ahi 32 * blo) 64 =
            ahi * blo).
    replace (unsigned_last_nbits ahi 32) with ahi
      by (symmetry; apply unsigned_last_nbits_eq; exact Ha1).
    rewrite unsigned_last_nbits_eq; [reflexivity | exact Hp2small].
  }
  assert (Hp3 : mulx_p3 a b = ahi * bhi).
  {
    unfold mulx_p3.
    change (unsigned_last_nbits
              (unsigned_last_nbits ahi 32 * unsigned_last_nbits bhi 32) 64 =
            ahi * bhi).
    replace (unsigned_last_nbits ahi 32) with ahi
      by (symmetry; apply unsigned_last_nbits_eq; exact Ha1).
    replace (unsigned_last_nbits bhi 32) with bhi
      by (symmetry; apply unsigned_last_nbits_eq; exact Hb1).
    rewrite unsigned_last_nbits_eq; [reflexivity | exact Hp3small].
  }
  assert (Hmid_range : 0 <= mulx_mid a b < U64_MOD).
  {
    unfold mulx_mid, U64_MOD.
    apply unsigned_Lastnbits_range; lia.
  }
  assert (Hmid_sum :
      mulx_p1 a b + mulx_p2 a b =
      mulx_mid a b + mid_carry * U64_MOD).
  {
    destruct Hmidcase as [[Hc Hlt] | [Hc Hge]]; subst mid_carry.
    - apply (u64_add_low_wrap (mulx_p1 a b) (mulx_p2 a b)).
      + rewrite Hp1; lia.
      + rewrite Hp1; lia.
      + rewrite Hp2; lia.
      + rewrite Hp2; lia.
      + unfold mulx_mid in Hlt.
        exact Hlt.
    - rewrite Z.mul_0_l, Z.add_0_r.
      apply (u64_add_low_no_wrap (mulx_p1 a b) (mulx_p2 a b)).
      + rewrite Hp1; lia.
      + rewrite Hp1; lia.
      + rewrite Hp2; lia.
      + rewrite Hp2; lia.
      + unfold mulx_mid in Hge.
        exact Hge.
  }
  set (mid_low := unsigned_last_nbits (mulx_mid a b) 32).
  set (mid_high := Z.shiftr (mulx_mid a b) 32).
  pose proof (u64_split_32 (mulx_mid a b) Hmid_range)
    as [Hmid_split [Hmid_low_range Hmid_high_range]].
  unfold mulx32_lo, mulx32_hi in Hmid_split, Hmid_low_range, Hmid_high_range.
  fold mid_low mid_high in Hmid_split, Hmid_low_range, Hmid_high_range.
  assert (Hmid_lo : mulx_mid_lo a b = mid_low * U32_MOD).
  {
    unfold mulx_mid_lo, unsigned_last_nbits.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Hmid_split.
    cbv [U32_MOD U64_MOD] in *.
    replace ((mid_low + mid_high * 2 ^ 32) * 2 ^ 32)
      with (2 ^ 64 * mid_high + mid_low * 2 ^ 32) by ring.
    symmetry.
    eapply (Z.mod_unique
      (2 ^ 64 * mid_high + mid_low * 2 ^ 32)
      (2 ^ 64) mid_high (mid_low * 2 ^ 32)).
    - left; lia.
    - ring.
  }
  assert (Hmid_hi : mulx_mid_hi a b mid_carry =
                   mid_high + mid_carry * U32_MOD).
  {
    unfold mulx_mid_hi.
    rewrite Z.shiftl_mul_pow2 by lia.
    fold mid_high.
    unfold U32_MOD.
    rewrite (unsigned_last_nbits_eq
      (mid_high + mid_carry * 2 ^ 32) 64).
    - reflexivity.
    - destruct Hmidcase as [[Hc _] | [Hc _]]; subst mid_carry;
        unfold U64_MOD in *; nia.
  }
  assert (Hmid_lo_range : 0 <= mulx_mid_lo a b < U64_MOD).
  {
    rewrite Hmid_lo.
    unfold U32_MOD, U64_MOD in *; nia.
  }
  assert (Hlo_range : 0 <= mulx_lo a b < U64_MOD).
  {
    unfold mulx_lo, U64_MOD.
    apply unsigned_Lastnbits_range; lia.
  }
  assert (Hlo_sum :
      mulx_p0 a b + mulx_mid_lo a b =
      mulx_lo a b + lo_carry * U64_MOD).
  {
    destruct Hlocase as [[Hc Hlt] | [Hc Hge]]; subst lo_carry.
    - rewrite Z.add_comm.
      replace (mulx_lo a b) with
        (unsigned_last_nbits (mulx_mid_lo a b + mulx_p0 a b) 64)
        by (unfold mulx_lo; rewrite Z.add_comm; reflexivity).
      apply (u64_add_low_wrap (mulx_mid_lo a b) (mulx_p0 a b)).
      + exact (proj1 Hmid_lo_range).
      + exact (proj2 Hmid_lo_range).
      + rewrite Hp0; lia.
      + rewrite Hp0; lia.
      + unfold mulx_lo in Hlt.
        rewrite Z.add_comm.
        exact Hlt.
    - rewrite Z.mul_0_l, Z.add_0_r.
      rewrite Z.add_comm.
      replace (mulx_lo a b) with
        (unsigned_last_nbits (mulx_mid_lo a b + mulx_p0 a b) 64)
        by (unfold mulx_lo; rewrite Z.add_comm; reflexivity).
      apply (u64_add_low_no_wrap (mulx_mid_lo a b) (mulx_p0 a b)).
      + exact (proj1 Hmid_lo_range).
      + exact (proj2 Hmid_lo_range).
      + rewrite Hp0; lia.
      + rewrite Hp0; lia.
      + unfold mulx_lo in Hge.
        rewrite Z.add_comm.
        exact Hge.
  }
  set (hi_raw := mulx_p3 a b + mulx_mid_hi a b mid_carry + lo_carry).
  assert (Hprod :
      a * b = mulx_lo a b + hi_raw * U64_MOD).
  {
    assert (Hrhs :
      mulx_lo a b + hi_raw * U64_MOD =
      mulx_p0 a b +
      (mulx_p1 a b + mulx_p2 a b) * U32_MOD +
      mulx_p3 a b * U64_MOD).
    {
      unfold hi_raw.
      rewrite Hmid_hi.
      replace (mulx_lo a b +
          (mulx_p3 a b + (mid_high + mid_carry * U32_MOD) + lo_carry)
            * U64_MOD)
        with ((mulx_lo a b + lo_carry * U64_MOD) +
          (mulx_p3 a b + mid_high + mid_carry * U32_MOD) * U64_MOD)
        by ring.
      rewrite <- Hlo_sum.
      rewrite Hmid_lo.
      replace (mulx_p0 a b + mid_low * U32_MOD +
          (mulx_p3 a b + mid_high + mid_carry * U32_MOD) * U64_MOD)
        with (mulx_p0 a b +
          (mid_low + mid_high * U32_MOD + mid_carry * U64_MOD) * U32_MOD +
          mulx_p3 a b * U64_MOD)
        by (replace U64_MOD with (U32_MOD * U32_MOD)
              by (cbv [U32_MOD U64_MOD]; reflexivity);
            ring).
      replace (mid_low + mid_high * U32_MOD + mid_carry * U64_MOD)
        with (mulx_mid a b + mid_carry * U64_MOD)
        by (rewrite Hmid_split; ring).
      rewrite <- Hmid_sum.
      reflexivity.
    }
    rewrite Hrhs.
    rewrite Hp0, Hp1, Hp2, Hp3.
    rewrite Ha_split, Hb_split.
    cbv [U32_MOD U64_MOD].
    ring.
  }
  assert (Hhi_raw_range : 0 <= hi_raw < U64_MOD).
  {
    assert (Hprod_bound : 0 <= a * b < U64_MOD * U64_MOD).
    {
      split.
      - apply Z.mul_nonneg_nonneg; lia.
      - apply Z.mul_lt_mono_nonneg; lia.
    }
    split.
    - unfold hi_raw.
      rewrite Hp3, Hmid_hi.
      destruct Hmidcase as [[Hmc _] | [Hmc _]];
      destruct Hlocase as [[Hlc _] | [Hlc _]];
      subst mid_carry lo_carry; lia.
    - destruct (Z_lt_ge_dec hi_raw U64_MOD) as [Hlt | Hge]; [exact Hlt |].
      assert (mulx_lo a b + hi_raw * U64_MOD >= U64_MOD * U64_MOD).
      {
        assert (U64_MOD * U64_MOD <= hi_raw * U64_MOD).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        lia.
      }
      lia.
  }
  assert (Hhi : mulx_hi a b mid_carry lo_carry = hi_raw).
  {
    unfold mulx_hi, hi_raw.
    assert (Hmidhi_lo_range :
      0 <= mulx_mid_hi a b mid_carry + lo_carry < U64_MOD).
    {
      rewrite Hmid_hi.
      destruct Hmidcase as [[Hmc _] | [Hmc _]];
      destruct Hlocase as [[Hlc _] | [Hlc _]];
      subst mid_carry lo_carry; lia.
    }
    rewrite (unsigned_last_nbits_eq
      (mulx_mid_hi a b mid_carry + lo_carry) 64 Hmidhi_lo_range).
    replace (mulx_p3 a b + (mulx_mid_hi a b mid_carry + lo_carry))
      with (mulx_p3 a b + mulx_mid_hi a b mid_carry + lo_carry)
      by ring.
    rewrite unsigned_last_nbits_eq; [reflexivity | exact Hhi_raw_range].
  }
  split; [exact Hlo_range |].
  split.
  - rewrite Hhi. exact Hhi_raw_range.
  - rewrite Hhi. exact Hprod.
Qed.

(** * Word-oriented Montgomery reduction facts *)

Lemma reduction_coefficient_step :
  forall p B i T coefficient accumulator digit next,
    accumulator = T + coefficient * p ->
    next = accumulator + digit * p * B ^ i ->
    next = T + (coefficient + digit * B ^ i) * p.
Proof.
  intros p B i T coefficient accumulator digit next
    Haccumulator Hnext.
  nia.
Qed.

Lemma low_word_cancellation :
  forall B p p_inv inverse_quotient
         input_word factor inverse_high
         product_low product_high output_word carry,
    1 < B ->
    p * p_inv + 1 = inverse_quotient * B ->
    input_word * p_inv = factor + inverse_high * B ->
    factor * p = product_low + product_high * B ->
    input_word + product_low = output_word + carry * B ->
    0 <= output_word < B ->
    output_word = 0.
Proof.
  intros B p p_inv inverse_quotient
    input_word factor inverse_high
    product_low product_high output_word carry
    HB Hinverse Hfactor Hproduct Houtput Houtput_range.
  assert (Hmultiple :
    input_word + factor * p =
      (input_word * inverse_quotient - inverse_high * p) * B).
  {
    assert (Hfactor_value :
      factor = input_word * p_inv - inverse_high * B) by lia.
    rewrite Hfactor_value.
    replace
      ((input_word * inverse_quotient - inverse_high * p) * B)
      with
      (input_word * (inverse_quotient * B) -
       inverse_high * B * p)
      by ring.
    rewrite <- Hinverse.
    ring.
  }
  assert (Houtput_multiple :
    output_word =
      (input_word * inverse_quotient - inverse_high * p -
       product_high - carry) * B).
  {
    replace
      ((input_word * inverse_quotient - inverse_high * p -
        product_high - carry) * B)
      with
      ((input_word * inverse_quotient - inverse_high * p) * B -
       product_high * B - carry * B)
      by ring.
    lia.
  }
  assert (Houtput_mod : output_word mod B = 0).
  {
    rewrite Houtput_multiple.
    apply Z.mod_mul.
    lia.
  }
  assert (Houtput_small : output_word mod B = output_word).
  {
    apply Z.mod_small.
    exact Houtput_range.
  }
  lia.
Qed.

Lemma sm2n_round_low_zero :
  forall x factor hi lo hi2 out carry,
    x * SM2_NEG_INV_N = factor + hi * U64_MOD ->
    factor * SM2_N0_Z = lo + hi2 * U64_MOD ->
    x + lo = out + carry * U64_MOD ->
    0 <= out < U64_MOD ->
    out = 0.
Proof.
  intros x factor hi lo hi2 out carry
    Hfactor Hproduct Houtput Hout.
  eapply low_word_cancellation
    with
      (B := U64_MOD)
      (p := SM2_N0_Z)
      (p_inv := SM2_NEG_INV_N)
      (inverse_quotient := SM2_NEG_INV_N_QUOTIENT)
      (input_word := x)
      (factor := factor)
      (inverse_high := hi)
      (product_low := lo)
      (product_high := hi2)
      (carry := carry).
  - cbv [U64_MOD].
    lia.
  - exact sm2_neg_inv_n0_multiple.
  - exact Hfactor.
  - exact Hproduct.
  - exact Houtput.
  - exact Hout.
Qed.

Lemma u576_low_1_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod U64_MOD = x0.
Proof.
  intros.
  unfold u576_of_limbs, u512_of_limbs in *.
  set (u := U64_MOD) in *.
  replace
    (x0 + x1 * u + x2 * u ^ 2 + x3 * u ^ 3 + x4 * u ^ 4 +
     x5 * u ^ 5 + x6 * u ^ 6 + x7 * u ^ 7 + x8 * u ^ 8)
    with
    (x0 + (x1 + x2 * u + x3 * u ^ 2 + x4 * u ^ 3 +
           x5 * u ^ 4 + x6 * u ^ 5 + x7 * u ^ 6 + x8 * u ^ 7) * u)
    by ring.
  rewrite Z.add_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_mul by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_small by (subst u; cbv [U64_MOD] in *; lia).
  reflexivity.
Qed.

Lemma u576_low_2_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod (U64_MOD ^ 2) =
    x0 + x1 * U64_MOD.
Proof.
  intros.
  unfold u576_of_limbs, u512_of_limbs in *.
  set (u := U64_MOD) in *.
  replace
    (x0 + x1 * u + x2 * u ^ 2 + x3 * u ^ 3 + x4 * u ^ 4 +
     x5 * u ^ 5 + x6 * u ^ 6 + x7 * u ^ 7 + x8 * u ^ 8)
    with
    (x0 + x1 * u +
     (x2 + x3 * u + x4 * u ^ 2 + x5 * u ^ 3 +
      x6 * u ^ 4 + x7 * u ^ 5 + x8 * u ^ 6) * u ^ 2)
    by ring.
  rewrite Z.add_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_mul by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_small by (subst u; cbv [U64_MOD] in *; nia).
  reflexivity.
Qed.

Lemma u576_low_3_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod (U64_MOD ^ 3) =
    x0 + x1 * U64_MOD + x2 * U64_MOD ^ 2.
Proof.
  intros.
  unfold u576_of_limbs, u512_of_limbs in *.
  set (u := U64_MOD) in *.
  replace
    (x0 + x1 * u + x2 * u ^ 2 + x3 * u ^ 3 + x4 * u ^ 4 +
     x5 * u ^ 5 + x6 * u ^ 6 + x7 * u ^ 7 + x8 * u ^ 8)
    with
    (x0 + x1 * u + x2 * u ^ 2 +
     (x3 + x4 * u + x5 * u ^ 2 + x6 * u ^ 3 +
      x7 * u ^ 4 + x8 * u ^ 5) * u ^ 3)
    by ring.
  rewrite Z.add_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_mul by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_small by (subst u; cbv [U64_MOD] in *; nia).
  reflexivity.
Qed.

Lemma u576_low_4_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod U256_MOD =
    x0 + x1 * U64_MOD + x2 * U64_MOD ^ 2 + x3 * U64_MOD ^ 3.
Proof.
  intros.
  unfold u576_of_limbs, u512_of_limbs in *.
  set (u := U64_MOD) in *.
  replace U256_MOD with (u ^ 4) by (subst u; cbv [U64_MOD U256_MOD]; ring).
  replace
    (x0 + x1 * u + x2 * u ^ 2 + x3 * u ^ 3 + x4 * u ^ 4 +
     x5 * u ^ 5 + x6 * u ^ 6 + x7 * u ^ 7 + x8 * u ^ 8)
    with
    (x0 + x1 * u + x2 * u ^ 2 + x3 * u ^ 3 +
     (x4 + x5 * u + x6 * u ^ 2 + x7 * u ^ 3 + x8 * u ^ 4) * u ^ 4)
    by ring.
  rewrite Z.add_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_mul by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by (subst u; cbv [U64_MOD]; lia).
  rewrite Z.mod_small by (subst u; cbv [U64_MOD] in *; nia).
  reflexivity.
Qed.

Lemma u576_low1_zero_from_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod U64_MOD = 0 ->
    x0 = 0.
Proof.
  intros.
  rewrite u576_low_1_mod in H0 by assumption.
  lia.
Qed.

Lemma u576_low2_zero_from_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod (U64_MOD ^ 2) = 0 ->
    x0 = 0 /\ x1 = 0.
Proof.
  intros.
  rewrite u576_low_2_mod in H1 by assumption.
  cbv [U64_MOD] in *.
  nia.
Qed.

Lemma u576_low3_zero_from_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod (U64_MOD ^ 3) = 0 ->
    x0 = 0 /\ x1 = 0 /\ x2 = 0.
Proof.
  intros.
  rewrite u576_low_3_mod in H2 by assumption.
  cbv [U64_MOD] in *.
  nia.
Qed.

Lemma u576_low4_zero_from_mod :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 mod U256_MOD = 0 ->
    x0 = 0 /\ x1 = 0 /\ x2 = 0 /\ x3 = 0.
Proof.
  intros.
  rewrite u576_low_4_mod in H3 by assumption.
  cbv [U64_MOD U256_MOD] in *.
  nia.
Qed.

Lemma u576_nonneg :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    0 <= x0 ->
    0 <= x1 ->
    0 <= x2 ->
    0 <= x3 ->
    0 <= x4 ->
    0 <= x5 ->
    0 <= x6 ->
    0 <= x7 ->
    0 <= x8 ->
    0 <= u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  intros.
  unfold u576_of_limbs, u512_of_limbs.
  assert (0 <= U64_MOD) by (cbv [U64_MOD]; lia).
  nia.
Qed.

Lemma u576_as_u256_high :
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8,
    u576_of_limbs x0 x1 x2 x3 x4 x5 x6 x7 x8 =
    u256_of_limbs x0 x1 x2 x3 +
    (u256_of_limbs x4 x5 x6 x7 + x8 * U256_MOD) * U256_MOD.
Proof.
  intros.
  cbv [u576_of_limbs u512_of_limbs u256_of_limbs U64_MOD U256_MOD].
  ring.
Qed.

Lemma sm2n_stage4_quotient_facts :
  forall T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0,
    0 <= t0 < U64_MOD ->
    0 <= t1 < U64_MOD ->
    0 <= t2 < U64_MOD ->
    0 <= t3 < U64_MOD ->
    0 <= t4 < U64_MOD ->
    0 <= t5 < U64_MOD ->
    0 <= t6 < U64_MOD ->
    0 <= t7 < U64_MOD ->
    0 <= t8 < U64_MOD ->
    sm2n_red_stage_4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) ->
    R0 = u256_of_limbs t4 t5 t6 t7 ->
    0 <= R0 < U256_MOD /\
    0 <= R0 + t8 * U256_MOD < 2 * SM2_N_Z /\
    exists q,
      0 <= q < U256_MOD /\
      (R0 + t8 * U256_MOD) * U256_MOD = T + q * SM2_N_Z.
Proof.
  intros T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0
    Ht0 Ht1 Ht2 Ht3 Ht4 Ht5 Ht6 Ht7 Ht8 Hstage HR0.
  unfold sm2n_red_stage_4, sm2n_red_stage in Hstage.
  destruct Hstage as
    [_ [[HT0 HT1] [q [[Hq0 Hq1] [Hv Hmod]]]]].
  rewrite sm2n_montgomery_radix in Hq1, Hmod.
  pose proof (u576_low4_zero_from_mod
    t0 t1 t2 t3 t4 t5 t6 t7 t8 Ht0 Ht1 Ht2 Ht3 Hmod)
    as [Et0 [Et1 [Et2 Et3]]].
  pose proof (u256_of_limbs_range t4 t5 t6 t7 Ht4 Ht5 Ht6 Ht7) as HR0_range.
  subst R0.
  subst t0 t1 t2 t3.
  assert (Hsplit :
    u576_of_limbs 0 0 0 0 t4 t5 t6 t7 t8 =
    (u256_of_limbs t4 t5 t6 t7 + t8 * U256_MOD) * U256_MOD).
  {
    rewrite u576_as_u256_high.
    cbv [u256_of_limbs].
    ring.
  }
  assert (HKmul :
    (u256_of_limbs t4 t5 t6 t7 + t8 * U256_MOD) * U256_MOD =
    T + q * SM2_N_Z) by lia.
  assert (HK0 : 0 <= u256_of_limbs t4 t5 t6 t7 + t8 * U256_MOD).
  {
    assert (0 <= U256_MOD) by (cbv [U256_MOD]; lia).
    nia.
  }
  assert (HKlt_mul :
    (u256_of_limbs t4 t5 t6 t7 + t8 * U256_MOD) * U256_MOD <
    2 * SM2_N_Z * U256_MOD).
  {
    rewrite HKmul.
    pose proof sm2_n_bounds as HN.
    clear - HT1 Hq1 HN.
    cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
         u256_of_limbs U32_MOD U64_MOD U256_MOD] in *.
    nia.
  }
  assert (HKlt :
    u256_of_limbs t4 t5 t6 t7 + t8 * U256_MOD < 2 * SM2_N_Z).
  {
    clear - HKlt_mul.
    cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
         u256_of_limbs U32_MOD U64_MOD U256_MOD] in *.
    nia.
  }
  split; [exact HR0_range |].
  split; [split; [exact HK0 | exact HKlt] |].
  exists q.
  split; [lia | exact HKmul].
Qed.

Lemma sm2n_stage4_no_sub_spec :
  forall T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0,
    0 <= t0 < U64_MOD ->
    0 <= t1 < U64_MOD ->
    0 <= t2 < U64_MOD ->
    0 <= t3 < U64_MOD ->
    0 <= t4 < U64_MOD ->
    0 <= t5 < U64_MOD ->
    0 <= t6 < U64_MOD ->
    0 <= t7 < U64_MOD ->
    0 <= t8 < U64_MOD ->
    t8 = 0 ->
    sm2n_red_stage_4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) ->
    R0 = u256_of_limbs t4 t5 t6 t7 ->
    R0 < SM2_N_Z ->
    sm2n_mont_red_spec T R0.
Proof.
  intros.
  pose proof (sm2n_stage4_quotient_facts
    T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0
    H H0 H1 H2 H3 H4 H5 H6 H7 H9 H10)
    as [HR0 [[HK0 HKlt] [q [Hq HKmul]]]].
  pose proof
    (sm2n_red_stage_input_bound 4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) H9)
    as HT.
  subst t8.
  unfold sm2n_mont_red_spec.
  repeat split; try lia.
  replace (R0 * U256_MOD - T) with (q * SM2_N_Z) by lia.
  apply Z.mod_mul.
  pose proof sm2_n_bounds.
  lia.
Qed.

Lemma sm2n_stage4_sub_t8_zero_spec :
  forall T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0 S carry,
    0 <= t0 < U64_MOD ->
    0 <= t1 < U64_MOD ->
    0 <= t2 < U64_MOD ->
    0 <= t3 < U64_MOD ->
    0 <= t4 < U64_MOD ->
    0 <= t5 < U64_MOD ->
    0 <= t6 < U64_MOD ->
    0 <= t7 < U64_MOD ->
    0 <= t8 < U64_MOD ->
    t8 = 0 ->
    sm2n_red_stage_4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) ->
    R0 = u256_of_limbs t4 t5 t6 t7 ->
    R0 >= SM2_N_Z ->
    0 <= S < U256_MOD ->
    0 <= carry <= 1 ->
    R0 + SM2_RHON_Z = S + carry * U256_MOD ->
    sm2n_mont_red_spec T S.
Proof.
  intros T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0 S carry
    Ht0 Ht1 Ht2 Ht3 Ht4 Ht5 Ht6 Ht7 Ht8
    Ht8zero Hstage HR0eq HR0ge HS_range Hcarry_range Hadd.
  pose proof (sm2n_stage4_quotient_facts
    T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0
    Ht0 Ht1 Ht2 Ht3 Ht4 Ht5 Ht6 Ht7 Ht8 Hstage HR0eq)
    as [HR0 [[HK0 HKlt] [q [Hq HKmul]]]].
  pose proof
    (sm2n_red_stage_input_bound 4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) Hstage)
    as HT.
  pose proof sm2_n_bounds as HN.
  pose proof sm2_rhon_is_neg_n as Hrho.
  subst t8.
  assert (carry = 1 /\ S = R0 - SM2_N_Z).
  {
    clear - HR0ge HS_range Hcarry_range Hadd HR0 HN Hrho.
    cbv [SM2_RHON_Z U256_MOD SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
         u256_of_limbs U32_MOD U64_MOD] in *.
    nia.
  }
  destruct H as [Hcarry HS].
  subst S.
  unfold sm2n_mont_red_spec.
  repeat split; try lia.
  replace ((R0 - SM2_N_Z) * U256_MOD - T)
    with ((q - U256_MOD) * SM2_N_Z) by lia.
  apply Z.mod_mul.
  pose proof sm2_n_bounds.
  lia.
Qed.

Lemma sm2n_stage4_sub_t8_nonzero_spec :
  forall T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0 S carry,
    0 <= t0 < U64_MOD ->
    0 <= t1 < U64_MOD ->
    0 <= t2 < U64_MOD ->
    0 <= t3 < U64_MOD ->
    0 <= t4 < U64_MOD ->
    0 <= t5 < U64_MOD ->
    0 <= t6 < U64_MOD ->
    0 <= t7 < U64_MOD ->
    0 <= t8 < U64_MOD ->
    t8 <> 0 ->
    sm2n_red_stage_4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) ->
    R0 = u256_of_limbs t4 t5 t6 t7 ->
    0 <= S < U256_MOD ->
    0 <= carry <= 1 ->
    R0 + SM2_RHON_Z = S + carry * U256_MOD ->
    sm2n_mont_red_spec T S /\ S < SM2_N_Z.
Proof.
  intros T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0 S carry
    Ht0 Ht1 Ht2 Ht3 Ht4 Ht5 Ht6 Ht7 Ht8
    Ht8nonzero Hstage HR0eq HS_range Hcarry_range Hadd.
  pose proof (sm2n_stage4_quotient_facts
    T t0 t1 t2 t3 t4 t5 t6 t7 t8 R0
    Ht0 Ht1 Ht2 Ht3 Ht4 Ht5 Ht6 Ht7 Ht8 Hstage HR0eq)
    as [HR0 [[HK0 HKlt] [q [Hq HKmul]]]].
  pose proof
    (sm2n_red_stage_input_bound 4 T
      (u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8) Hstage)
    as HT.
  pose proof sm2_n_bounds as HN.
  pose proof sm2_rhon_is_neg_n as Hrho.
  assert (t8 = 1 /\ R0 < SM2_N_Z /\ carry = 0 /\
          S = R0 + U256_MOD - SM2_N_Z).
  {
    clear - Ht8 Ht8nonzero HS_range Hcarry_range Hadd HR0 HK0 HKlt HN Hrho.
    cbv [SM2_RHON_Z U256_MOD SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
         u256_of_limbs U32_MOD U64_MOD] in *.
    nia.
  }
  destruct H as [Ht8one [HR0lt [Hcarry HS]]].
  subst t8 S carry.
  split.
  - unfold sm2n_mont_red_spec.
    repeat split; try lia.
    replace ((R0 + U256_MOD - SM2_N_Z) * U256_MOD - T)
      with ((q - U256_MOD) * SM2_N_Z) by lia.
    apply Z.mod_mul.
    pose proof sm2_n_bounds.
    lia.
  - lia.
Qed.

Lemma store_u256_zero_pack :
  forall p,
    ((&((p) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) # UInt64 |-> 0) **
    ((&((p) # "u32" ->ₛ "v") + (1 * sizeof(UINT64))) # UInt64 |-> 0) **
    ((&((p) # "u32" ->ₛ "v") + (2 * sizeof(UINT64))) # UInt64 |-> 0) **
    ((&((p) # "u32" ->ₛ "v") + (3 * sizeof(UINT64))) # UInt64 |-> 0)
    |-- store_u256 p 0.
Proof.
  intros.
  unfold store_u256, store_u256_limbs.
  Exists 0 0 0 0.
  split_pure_spatial.
  - entailer!.
  - cbv [u256_of_limbs U64_MOD].
    entailer!.
Qed.

Lemma sm2n_add_round_shift1_chain :
  forall t0 t1 t2 t3 t4 t5 t6 t7 t8
         factor
         l0 h0 o1 c1 a2 c2 a3 c3 a4 c4 a5 c5 a6 c6 a7 c7 a8 c8
         l1 h1 o2 c9 b3 c10 b4 c11 b5 c12 b6 c13 b7 c14 b8 c15
         l2 h2 o3 c16 c5a c17 c6a c18 c7a c19 c8a c20 c9a c21
         l3 h3 o4 c22 o5 c23 o6 c24 o7 c25 o8 c26,
    factor * SM2_N0_Z = l0 + h0 * U64_MOD ->
    t1 + l0 + 0 = o1 + c1 * U64_MOD ->
    t2 + h0 + c1 = a2 + c2 * U64_MOD ->
    t3 + 0 + c2 = a3 + c3 * U64_MOD ->
    t4 + 0 + c3 = a4 + c4 * U64_MOD ->
    t5 + 0 + c4 = a5 + c5 * U64_MOD ->
    t6 + 0 + c5 = a6 + c6 * U64_MOD ->
    t7 + 0 + c6 = a7 + c7 * U64_MOD ->
    t8 + 0 + c7 = a8 + c8 * U64_MOD ->
    factor * SM2_N1_Z = l1 + h1 * U64_MOD ->
    a2 + l1 + 0 = o2 + c9 * U64_MOD ->
    a3 + h1 + c9 = b3 + c10 * U64_MOD ->
    a4 + 0 + c10 = b4 + c11 * U64_MOD ->
    a5 + 0 + c11 = b5 + c12 * U64_MOD ->
    a6 + 0 + c12 = b6 + c13 * U64_MOD ->
    a7 + 0 + c13 = b7 + c14 * U64_MOD ->
    a8 + 0 + c14 = b8 + c15 * U64_MOD ->
    factor * SM2_N2_Z = l2 + h2 * U64_MOD ->
    b3 + l2 + 0 = o3 + c16 * U64_MOD ->
    b4 + h2 + c16 = c5a + c17 * U64_MOD ->
    b5 + 0 + c17 = c6a + c18 * U64_MOD ->
    b6 + 0 + c18 = c7a + c19 * U64_MOD ->
    b7 + 0 + c19 = c8a + c20 * U64_MOD ->
    b8 + 0 + c20 = c9a + c21 * U64_MOD ->
    factor * SM2_N3_Z = l3 + h3 * U64_MOD ->
    c5a + l3 + 0 = o4 + c22 * U64_MOD ->
    c6a + h3 + c22 = o5 + c23 * U64_MOD ->
    c7a + 0 + c23 = o6 + c24 * U64_MOD ->
    c8a + 0 + c24 = o7 + c25 * U64_MOD ->
    c9a + 0 + c25 = o8 + c26 * U64_MOD ->
    u576_of_limbs t0 o1 o2 o3 o4 o5 o6 o7 o8 +
      (c8 + c15 + c21 + c26) * U64_MOD ^ 9 =
    u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8 +
      factor * SM2_N_Z * U64_MOD.
Proof.
  intros.
  cbv [u576_of_limbs u512_of_limbs u256_of_limbs
       SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       U32_MOD U64_MOD] in *.
  lia.
Qed.

Lemma sm2n_add_round_shift2_chain :
  forall t0 t1 t2 t3 t4 t5 t6 t7 t8
         factor
         l0 h0 o2 c1 a3 c2 a4 c3 a5 c4 a6 c5 a7 c6 a8 c7
         l1 h1 o3 c8 b4 c9 b5 c10 b6 c11 b7 c12 b8 c13
         l2 h2 o4 c14 c5a c15 c6a c16 c7a c17 c8a c18
         l3 h3 o5 c19 o6 c20 o7 c21 o8 c22,
    factor * SM2_N0_Z = l0 + h0 * U64_MOD ->
    t2 + l0 + 0 = o2 + c1 * U64_MOD ->
    t3 + h0 + c1 = a3 + c2 * U64_MOD ->
    t4 + 0 + c2 = a4 + c3 * U64_MOD ->
    t5 + 0 + c3 = a5 + c4 * U64_MOD ->
    t6 + 0 + c4 = a6 + c5 * U64_MOD ->
    t7 + 0 + c5 = a7 + c6 * U64_MOD ->
    t8 + 0 + c6 = a8 + c7 * U64_MOD ->
    factor * SM2_N1_Z = l1 + h1 * U64_MOD ->
    a3 + l1 + 0 = o3 + c8 * U64_MOD ->
    a4 + h1 + c8 = b4 + c9 * U64_MOD ->
    a5 + 0 + c9 = b5 + c10 * U64_MOD ->
    a6 + 0 + c10 = b6 + c11 * U64_MOD ->
    a7 + 0 + c11 = b7 + c12 * U64_MOD ->
    a8 + 0 + c12 = b8 + c13 * U64_MOD ->
    factor * SM2_N2_Z = l2 + h2 * U64_MOD ->
    b4 + l2 + 0 = o4 + c14 * U64_MOD ->
    b5 + h2 + c14 = c5a + c15 * U64_MOD ->
    b6 + 0 + c15 = c6a + c16 * U64_MOD ->
    b7 + 0 + c16 = c7a + c17 * U64_MOD ->
    b8 + 0 + c17 = c8a + c18 * U64_MOD ->
    factor * SM2_N3_Z = l3 + h3 * U64_MOD ->
    c5a + l3 + 0 = o5 + c19 * U64_MOD ->
    c6a + h3 + c19 = o6 + c20 * U64_MOD ->
    c7a + 0 + c20 = o7 + c21 * U64_MOD ->
    c8a + 0 + c21 = o8 + c22 * U64_MOD ->
    u576_of_limbs t0 t1 o2 o3 o4 o5 o6 o7 o8 +
      (c7 + c13 + c18 + c22) * U64_MOD ^ 9 =
    u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8 +
      factor * SM2_N_Z * U64_MOD ^ 2.
Proof.
  intros.
  cbv [u576_of_limbs u512_of_limbs u256_of_limbs
       SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       U32_MOD U64_MOD] in *.
  lia.
Qed.

Lemma sm2n_add_round_shift3_chain :
  forall t0 t1 t2 t3 t4 t5 t6 t7 t8
         factor
         l0 h0 o3 c1 a4 c2 a5 c3 a6 c4 a7 c5 a8 c6
         l1 h1 o4 c7 b5 c8 b6 c9 b7 c10 b8 c11
         l2 h2 o5 c12 c6a c13 c7a c14 c8a c15
         l3 h3 o6 c16 o7 c17 o8 c18,
    factor * SM2_N0_Z = l0 + h0 * U64_MOD ->
    t3 + l0 + 0 = o3 + c1 * U64_MOD ->
    t4 + h0 + c1 = a4 + c2 * U64_MOD ->
    t5 + 0 + c2 = a5 + c3 * U64_MOD ->
    t6 + 0 + c3 = a6 + c4 * U64_MOD ->
    t7 + 0 + c4 = a7 + c5 * U64_MOD ->
    t8 + 0 + c5 = a8 + c6 * U64_MOD ->
    factor * SM2_N1_Z = l1 + h1 * U64_MOD ->
    a4 + l1 + 0 = o4 + c7 * U64_MOD ->
    a5 + h1 + c7 = b5 + c8 * U64_MOD ->
    a6 + 0 + c8 = b6 + c9 * U64_MOD ->
    a7 + 0 + c9 = b7 + c10 * U64_MOD ->
    a8 + 0 + c10 = b8 + c11 * U64_MOD ->
    factor * SM2_N2_Z = l2 + h2 * U64_MOD ->
    b5 + l2 + 0 = o5 + c12 * U64_MOD ->
    b6 + h2 + c12 = c6a + c13 * U64_MOD ->
    b7 + 0 + c13 = c7a + c14 * U64_MOD ->
    b8 + 0 + c14 = c8a + c15 * U64_MOD ->
    factor * SM2_N3_Z = l3 + h3 * U64_MOD ->
    c6a + l3 + 0 = o6 + c16 * U64_MOD ->
    c7a + h3 + c16 = o7 + c17 * U64_MOD ->
    c8a + 0 + c17 = o8 + c18 * U64_MOD ->
    u576_of_limbs t0 t1 t2 o3 o4 o5 o6 o7 o8 +
      (c6 + c11 + c15 + c18) * U64_MOD ^ 9 =
    u576_of_limbs t0 t1 t2 t3 t4 t5 t6 t7 t8 +
      factor * SM2_N_Z * U64_MOD ^ 3.
Proof.
  intros.
  cbv [u576_of_limbs u512_of_limbs u256_of_limbs
       SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       U32_MOD U64_MOD] in *.
  lia.
Qed.

Lemma sm2n_stage_value_bound_u1 :
  forall t q,
    0 <= t < SM2_N_Z * U256_MOD ->
    0 <= q < U64_MOD ->
    t + q * SM2_N_Z < U64_MOD ^ 9.
Proof.
  intros.
  cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       u256_of_limbs U32_MOD U64_MOD U256_MOD] in *.
  lia.
Qed.

Lemma sm2n_stage_value_bound_u2 :
  forall t q,
    0 <= t < SM2_N_Z * U256_MOD ->
    0 <= q < U64_MOD ^ 2 ->
    t + q * SM2_N_Z < U64_MOD ^ 9.
Proof.
  intros.
  cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       u256_of_limbs U32_MOD U64_MOD U256_MOD] in *.
  lia.
Qed.

Lemma sm2n_stage_value_bound_u3 :
  forall t q,
    0 <= t < SM2_N_Z * U256_MOD ->
    0 <= q < U64_MOD ^ 3 ->
    t + q * SM2_N_Z < U64_MOD ^ 9.
Proof.
  intros.
  cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       u256_of_limbs U32_MOD U64_MOD U256_MOD] in *.
  lia.
Qed.

Lemma sm2n_stage_value_bound_u4 :
  forall t q,
    0 <= t < SM2_N_Z * U256_MOD ->
    0 <= q < U256_MOD ->
    t + q * SM2_N_Z < U64_MOD ^ 9.
Proof.
  intros.
  cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       u256_of_limbs U32_MOD U64_MOD U256_MOD] in *.
  lia.
Qed.

Lemma sm2n_mul_bound :
  forall x y,
    0 <= x < SM2_N_Z ->
    0 <= y < SM2_N_Z ->
    0 <= x * y < SM2_N_Z * U256_MOD.
Proof.
  intros x y Hx Hy.
  pose proof sm2_n_bounds.
  nia.
Qed.

Ltac solve_u32_ge_after a0 a1 a2 a3 b0 b1 b2 b3 :=
  unfold store_u256, store_u256_limbs;
  Exists a0 a1 a2 a3 b0 b1 b2 b3;
  entailer!;
  cbv [u256_of_limbs U64_MOD] in *;
  nia.

Ltac prepare_sub_math a0 a1 a2 a3 b0 b1 b2 b3
     r0 r1 r2 r3 c1 c2 c3 c4 h0 h1 h2 h3 hB hA :=
  rewrite (unsigned_lnot_u64 b0 ltac:(lia)) in h0;
  rewrite (unsigned_lnot_u64 b1 ltac:(lia)) in h1;
  rewrite (unsigned_lnot_u64 b2 ltac:(lia)) in h2;
  rewrite (unsigned_lnot_u64 b3 ltac:(lia)) in h3;
  pose proof (u32_sub_chain4
    a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3
    c1 c2 c3 c4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    h0 h1 h2 h3) as Hsub;
  destruct Hsub as (S & borrow & HS & Hb & HE & ->);
  rewrite <- hA, <- hB in HE.

Ltac solve_sub_pure limb :=
  pre_process;
  pose proof (unsigned_lnot_u64_range limb ltac:(lia));
  entailer!.

Ltac solve_raw_pow_partial :=
  aggressive_pre_process;
  first
      [ match goal with
        | |- context [Z.lor (unsigned_last_nbits (Z.shiftl ?hi 1) 64)
                              (Z.shiftr ?lo 63)] =>
            assert (Hhi_range : 0 <= hi < U64_MOD) by entailer!;
            assert (Hlo_range : 0 <= lo < U64_MOD) by entailer!;
            pose proof
              (u64_double_lor_range hi lo Hhi_range Hlo_range) as Hrange
        end;
        entailer!
      | match goal with
        | |- context [unsigned_last_nbits ?x 64] =>
            pose proof
              (unsigned_Lastnbits_range x 64 ltac:(lia)) as Hrange;
            change (0 <= unsigned_last_nbits x 64 < U64_MOD) in Hrange
        end;
        entailer!
      | match goal with
        | |- context [unsigned_last_nbits ?x 8] =>
            pose proof
              (unsigned_Lastnbits_range x 8 ltac:(lia)) as Hrange;
            assert (Hbyte_lt_u64 : 2 ^ 8 < U64_MOD)
              by (unfold U64_MOD; lia)
        end;
        entailer!
      | entailer!
      ].
