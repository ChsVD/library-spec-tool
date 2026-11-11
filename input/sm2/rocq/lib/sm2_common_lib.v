Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SumLib Require Import SumLib.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export u32_def limb_arithmetic.
From SimpleC.EE.Applications_human.sm2.lib
  Require Export montgomery.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Import Snaive_C_Rules.
Local Open Scope sac.

Notation "'Zmod'" := Z.modulo.

(** Integer and memory representations used by the SM2 implementation. *)

(** * Shared word moduli *)

Definition U64_MOD : Z := 2 ^ 64.
Definition U32_MOD : Z := 2 ^ 32.
Definition U256_MOD : Z := 2 ^ 256.
Definition U512_MOD : Z := U256_MOD * U256_MOD.

Lemma U64_MOD_as_U32_MOD_squared :
  U64_MOD = U32_MOD * U32_MOD.
Proof. vm_compute. reflexivity. Qed.

(** * Fixed four-limb 256-bit representation *)

(** Four little-endian 64-bit limbs interpreted as one 256-bit integer. *)
Definition u256_of_limbs (x0 x1 x2 x3 : Z) : Z :=
  x0 + x1 * U64_MOD + x2 * U64_MOD ^ 2 + x3 * U64_MOD ^ 3.

Lemma u256_of_limbs_nested :
  forall x0 x1 x2 x3,
    u256_of_limbs x0 x1 x2 x3 =
      x0 + U64_MOD * (x1 + U64_MOD * (x2 + U64_MOD * x3)).
Proof.
  intros.
  unfold u256_of_limbs.
  ring.
Qed.

Lemma u256_of_limbs_injective :
  forall a0 a1 a2 a3 b0 b1 b2 b3,
    0 <= a0 < U64_MOD ->
    0 <= a1 < U64_MOD ->
    0 <= a2 < U64_MOD ->
    0 <= a3 < U64_MOD ->
    0 <= b0 < U64_MOD ->
    0 <= b1 < U64_MOD ->
    0 <= b2 < U64_MOD ->
    0 <= b3 < U64_MOD ->
    u256_of_limbs a0 a1 a2 a3 = u256_of_limbs b0 b1 b2 b3 ->
    a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intros a0 a1 a2 a3 b0 b1 b2 b3
    Ha0 Ha1 Ha2 Ha3 Hb0 Hb1 Hb2 Hb3 Heq.
  rewrite !u256_of_limbs_nested in Heq.
  assert (Hbase : 0 < U64_MOD) by (cbv [U64_MOD]; lia).
  destruct (radix_step_unique
    U64_MOD a0
      (a1 + U64_MOD * (a2 + U64_MOD * a3))
    b0
      (b1 + U64_MOD * (b2 + U64_MOD * b3))
    Hbase Ha0 Hb0 Heq) as [H0 Heq1].
  destruct (radix_step_unique
    U64_MOD a1 (a2 + U64_MOD * a3)
    b1 (b2 + U64_MOD * b3)
    Hbase Ha1 Hb1 Heq1) as [H1 Heq2].
  destruct (radix_step_unique
    U64_MOD a2 a3 b2 b3
    Hbase Ha2 Hb2 Heq2) as [H2 H3].
  repeat split; assumption.
Qed.

Lemma u256_of_limbs_range :
  forall x0 x1 x2 x3,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= u256_of_limbs x0 x1 x2 x3 < U256_MOD.
Proof.
  intros.
  cbv [u256_of_limbs U64_MOD U256_MOD] in *.
  lia.
Qed.

(** Ownership of exactly four 64-bit limbs beginning at [base]. *)
Definition store_u256_limbs (base : addr) (x : Z) : Assertion :=
  EX x0 x1 x2 x3,
    “ 0 <= x0 < U64_MOD /\
       0 <= x1 < U64_MOD /\
       0 <= x2 < U64_MOD /\
       0 <= x3 < U64_MOD /\
       x = u256_of_limbs x0 x1 x2 x3 ” &&
    ((base + (0 * sizeof(UINT64))) # UInt64 |-> x0) **
    ((base + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
    ((base + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
    ((base + (3 * sizeof(UINT64))) # UInt64 |-> x3).

(** Ownership of one complete named C [u32] object. *)
Definition store_u256 (address : addr) (x : Z) : Assertion :=
  store_u256_limbs (&((address) # "u32" ->ₛ "v")) x.

Lemma store_u256_value_range :
  forall address value,
    store_u256 address value |-- “ 0 <= value < U256_MOD ”.
Proof.
  intros address value.
  unfold store_u256, store_u256_limbs.
  Intros x0 x1 x2 x3.
  entailer!.
  all: destruct H as [H0 [H1 [H2 [H3 Hvalue]]]];
       subst value;
       destruct (u256_of_limbs_range x0 x1 x2 x3 H0 H1 H2 H3);
       assumption.
Qed.

(** Explicitly approved layout assumption for the verification wrapper that
    casts a pointer to the first [u32.v] limb back to [u32 *]. *)
Axiom u32_v_field_address_eq :
  forall address : addr,
    &((address) # "u32" ->ₛ "v") = address.

Lemma global_u32_v_addr_eq :
  forall name : string,
    eval_addr_expr
      (RE_addr_of (LE_arrow_field (RE_addr_of (LE_var name)) "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_arrow_field
          (RE_const
            (eval_addr_expr (RE_addr_of (LE_var name)))
            (FET_alias "u32"))
          "v")).
Proof.
  intros.
  csimpl.
  reflexivity.
Qed.

(** A canonical residue stored in one [u32] object. *)
Definition store_mod
    (modulus : Z) (address : addr) (x : Z) : Assertion :=
  “ 0 <= x < modulus ” && store_u256 address x.

Lemma four_u64_cells_to_undef_full :
  forall base x0 x1 x2 x3,
    ((base + (0 * sizeof(UINT64))) # UInt64 |-> x0) **
    ((base + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
    ((base + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
    ((base + (3 * sizeof(UINT64))) # UInt64 |-> x3)
    |-- UInt64Array.undef_full base 4.
Proof.
  intros base x0 x1 x2 x3.
  assert (Hfull :
    ((base + (0 * sizeof(UINT64))) # UInt64 |-> x0) **
    ((base + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
    ((base + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
    ((base + (3 * sizeof(UINT64))) # UInt64 |-> x3)
    |-- UInt64Array.full base 4 (x0 :: x1 :: x2 :: x3 :: nil)).
  {
    unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
  }
  sep_apply Hfull.
  sep_apply UInt64Array.full_to_undef_full.
  entailer!.
Qed.

(** A whole-record assignment can leave the overwritten high limb canceled
    from both sides of a VC.  Recover the three owned low limbs from the
    resulting array predicate without expanding unrelated array predicates. *)
Lemma u256_missing_high_limb_to_low_cells :
  forall base x0 x1 x2 x3,
    UInt64Array.missing_i base 3 0 4
      (x0 :: x1 :: x2 :: x3 :: nil)
    |-- ((base + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
        ((base + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
        ((base + (0 * sizeof(UINT64))) # UInt64 |-> x0).
Proof.
  intros base x0 x1 x2 x3.
  rewrite (UInt64Array.missing_i_unfold base 3 0 4
    (x1 :: x2 :: x3 :: nil) x0).
  Split.
  - entailer!.
  - rewrite (UInt64Array.missing_i_unfold base 3 1 4
      (x2 :: x3 :: nil) x1).
    entailer!.
    Split.
    + entailer!.
    + rewrite (UInt64Array.missing_i_unfold base 3 2 4
        (x3 :: nil) x2).
      entailer!.
      Split.
      * entailer!.
      * rewrite (UInt64Array.missing_i_unfold base 3 3 4 nil x3).
        entailer!.
        Split; entailer!.
        rewrite UInt64Array.seg_empty; entailer!.
Qed.

Lemma store_u256_limbs_to_undef_full :
  forall base x,
    store_u256_limbs base x |-- UInt64Array.undef_full base 4.
Proof.
  intros base x.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3.
  sep_apply (four_u64_cells_to_undef_full base x0 x1 x2 x3).
  entailer!.
Qed.

Lemma store_u256_to_undef :
  forall address x,
    store_u256 address x |-- UndefStructPredu32 address.
Proof.
  intros address x.
  unfold store_u256, UndefStructPredu32.
  apply store_u256_limbs_to_undef_full.
Qed.

Lemma store_u256_undef_conflict :
  forall address x,
    store_u256 address x ** UndefStructPredu32 address |-- “ False ”.
Proof.
  intros address x.
  unfold store_u256, store_u256_limbs, UndefStructPredu32.
  Intros x0 x1 x2 x3.
  unfold UInt64Array.undef_full, store_undef_array.
  simpl store_undef_array_rec.
  unfold store_uint64, undef_store_uint64.
  rewrite Z.mul_0_l.
  Intros.
  sep_apply store_8byte_store_8byte_noinit.
  sep_apply dup_store_8bytes_noninit.
  entailer!.
Qed.

Lemma store_u256_undef_neq :
  forall stored_address undef_address x,
    store_u256 stored_address x ** UndefStructPredu32 undef_address
    |-- “ stored_address <> undef_address ”.
Proof.
  intros stored_address undef_address x.
  destruct (Z.eq_dec stored_address undef_address) as [Heq | Hneq].
  - subst undef_address.
    sep_apply (store_u256_undef_conflict stored_address x).
    entailer!.
  - entailer!.
Qed.

Lemma store_mod_base0_pack :
  forall modulus address x,
    0 <= x < modulus ->
    store_u256_limbs
      (&((address) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) x
    |-- store_mod modulus address x.
Proof.
  intros modulus address x Hx.
  unfold store_mod, store_u256.
  rewrite sizeof_uint64.
  replace (&((address) # "u32" ->ₛ "v") + 0 * 8)
    with (&((address) # "u32" ->ₛ "v")) by lia.
  entailer!.
Qed.

Lemma store_mod_base0_unpack :
  forall modulus address x,
    store_mod modulus address x |--
    “ 0 <= x < modulus ” &&
    store_u256_limbs
      (&((address) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) x.
Proof.
  intros modulus address x.
  unfold store_mod, store_u256.
  rewrite sizeof_uint64.
  replace (&((address) # "u32" ->ₛ "v") + 0 * 8)
    with (&((address) # "u32" ->ₛ "v")) by lia.
  entailer!.
Qed.

(** * Variable-width little-endian limb arrays *)

(** Little-endian lists of 64-bit limbs. *)
Definition u64_list_value (xs : list Z) : Z :=
  limb_list_value U64_MOD xs.

Definition u64_list_bounded (xs : list Z) : Prop :=
  limb_list_bounded U64_MOD xs.

Lemma u64_list_value_four :
  forall x0 x1 x2 x3,
    u64_list_value (x0 :: x1 :: x2 :: x3 :: nil) =
    u256_of_limbs x0 x1 x2 x3.
Proof.
  intros x0 x1 x2 x3.
  unfold u64_list_value, u256_of_limbs.
  repeat rewrite limb_list_value_cons.
  rewrite limb_list_value_nil.
  ring.
Qed.

Lemma uint64_full4_to_store_u256_limbs :
  forall base xs,
    UInt64Array.full base 4 xs |--
      store_u256_limbs base (u64_list_value xs).
Proof.
  intros base xs.
  prop_apply (UInt64Array.full_Zlength base 4 xs).
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
  prop_apply (store_uint64_range (base + 0 * sizeof(UINT64)) x0).
  Intros.
  prop_apply (store_uint64_range (base + 1 * sizeof(UINT64)) x1).
  Intros.
  prop_apply (store_uint64_range (base + 2 * sizeof(UINT64)) x2).
  Intros.
  prop_apply (store_uint64_range (base + 3 * sizeof(UINT64)) x3).
  Intros.
  unfold store_u256_limbs.
  Exists x0 x1 x2 x3.
  entailer!.
  - change (0 <= x0 <= U64_MOD - 1) in H2; lia.
  - change (0 <= x1 <= U64_MOD - 1) in H3; lia.
  - change (0 <= x2 <= U64_MOD - 1) in H4; lia.
  - change (0 <= x3 <= U64_MOD - 1) in H5; lia.
  - unfold u64_list_value, u256_of_limbs.
    repeat rewrite limb_list_value_cons.
    rewrite limb_list_value_nil.
    ring.
Qed.

Lemma uint64_full4_bounded :
  forall base xs,
    UInt64Array.full base 4 xs |-- “ u64_list_bounded xs ”.
Proof.
  intros base xs.
  prop_apply (UInt64Array.full_Zlength base 4 xs).
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
  prop_apply (store_uint64_range (base + 0 * sizeof(UINT64)) x0).
  Intros.
  prop_apply (store_uint64_range (base + 1 * sizeof(UINT64)) x1).
  Intros.
  prop_apply (store_uint64_range (base + 2 * sizeof(UINT64)) x2).
  Intros.
  prop_apply (store_uint64_range (base + 3 * sizeof(UINT64)) x3).
  Intros.
  replace Int64.max_unsigned with 18446744073709551615 in * by reflexivity.
  entailer!.
  unfold u64_list_bounded.
  repeat rewrite limb_list_bounded_cons_iff.
  split; [cbv [U64_MOD]; lia |].
  split; [cbv [U64_MOD]; lia |].
  split; [cbv [U64_MOD]; lia |].
  split; [cbv [U64_MOD]; lia |].
  unfold limb_list_bounded.
  intros i Hi.
  rewrite Zlength_nil in Hi.
  lia.
Qed.

Lemma store_u256_limbs_to_uint64_full4 :
  forall base x xs,
    Zlength xs = 4 ->
    u64_list_bounded xs ->
    u64_list_value xs = x ->
    store_u256_limbs base x |-- UInt64Array.full base 4 xs.
Proof.
  intros base x xs Hlength Hbounded Hvalue.
  destruct xs as [|b0 xs].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct xs as [|b1 xs].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct xs as [|b2 xs].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct xs as [|b3 xs].
  { rewrite Zlength_nil in Hlength; lia. }
  rewrite Zlength_cons in Hlength.
  destruct xs as [|b4 xs].
  2: {
    rewrite Zlength_cons in Hlength.
    pose proof (Zlength_nonneg xs).
    lia.
  }
  apply limb_list_bounded_cons_iff in Hbounded as [Hb0 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb1 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb2 Hbounded].
  apply limb_list_bounded_cons_iff in Hbounded as [Hb3 Hbounded].
  rewrite u64_list_value_four in Hvalue.
  unfold store_u256_limbs.
  Intros a0 a1 a2 a3.
  destruct H as [Ha0 [Ha1 [Ha2 [Ha3 Hstored]]]].
  assert (Hequal :
    u256_of_limbs a0 a1 a2 a3 =
    u256_of_limbs b0 b1 b2 b3) by lia.
  destruct (u256_of_limbs_injective
    a0 a1 a2 a3 b0 b1 b2 b3
    Ha0 Ha1 Ha2 Ha3 Hb0 Hb1 Hb2 Hb3 Hequal)
    as [-> [-> [-> ->]]].
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer!.
Qed.

(** Materialize a complete [u32] value as the exact four-limb array required
    by a whole-record C assignment. *)
Lemma store_u256_materialize_full :
  forall address x,
    store_u256 address x |--
      EX xs,
        “ Zlength xs = 4 /\
          u64_list_bounded xs /\
          u64_list_value xs = x ” &&
        UInt64Array.full (&((address) # "u32" ->ₛ "v")) 4 xs.
Proof.
  intros address x.
  unfold store_u256, store_u256_limbs.
  Intros x0 x1 x2 x3.
  destruct H as [Hx0 [Hx1 [Hx2 [Hx3 Hvalue]]]].
  Exists [x0; x1; x2; x3].
  assert (Hbounded : u64_list_bounded [x0; x1; x2; x3]).
  {
    unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    repeat split; try assumption.
    all: cbn in *; lia.
  }
  rewrite u64_list_value_four.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer!.
Qed.

Definition record_u32_well_formed (record : Recordu32) : Prop :=
  Zlength record.(u32_v) = 4 /\
  u64_list_bounded record.(u32_v).

Lemma StructPredu32_well_formed :
  forall address record,
    StructPredu32 address record |-- “ record_u32_well_formed record ”.
Proof.
  intros address record.
  unfold StructPredu32, record_u32_well_formed.
  prop_apply
    (UInt64Array.full_Zlength
      (&(address # "u32" ->ₛ "v")) 4 record.(u32_v)).
  Intros.
  prop_apply
    (uint64_full4_bounded
      (&(address # "u32" ->ₛ "v")) record.(u32_v)).
  entailer!.
Qed.

Lemma store_u256_to_StructPredu32 :
  forall address x record,
    record_u32_well_formed record ->
    u64_list_value record.(u32_v) = x ->
    store_u256 address x |-- StructPredu32 address record.
Proof.
  intros address x [xs] [Hlength Hbounded] Hvalue.
  unfold store_u256, StructPredu32.
  cbn [u32_v] in *.
  apply store_u256_limbs_to_uint64_full4;
    assumption.
Qed.

(** Little-endian lists of 32-bit limbs. *)
Definition u32_list_value (xs : list Z) : Z :=
  limb_list_value U32_MOD xs.

Definition u32_list_bounded (xs : list Z) : Prop :=
  limb_list_bounded U32_MOD xs.

(** Place value after [i] 64-bit limbs. *)
Definition U64_POW (i : Z) : Z := U64_MOD ^ i.

Lemma U64_POW_succ :
  forall i, 0 <= i -> U64_POW (i + 1) = U64_POW i * U64_MOD.
Proof.
  intros i Hi.
  change
    (limb_radix U64_MOD (i + 1) =
      limb_radix U64_MOD i * U64_MOD).
  apply limb_radix_succ.
  exact Hi.
Qed.

Lemma U64_POW_nonneg : forall i, 0 <= U64_POW i.
Proof.
  intros i.
  change (0 <= limb_radix U64_MOD i).
  apply limb_radix_nonneg.
  cbv [U64_MOD].
  lia.
Qed.

Lemma U256_MOD_as_U64_POW_4 : U256_MOD = U64_POW 4.
Proof. vm_compute. reflexivity. Qed.

Lemma unsigned_last_nbits_u64_small :
  forall x, 0 <= x < U64_MOD -> unsigned_last_nbits x 64 = x.
Proof.
  intros x Hx.
  apply unsigned_last_nbits_eq.
  exact Hx.
Qed.

(** * Relations between 32-bit, 64-bit, and 256-bit representations *)

Lemma u32_pair_range :
  forall low high,
    0 <= low < U32_MOD ->
    0 <= high < U32_MOD ->
    0 <= low + high * U32_MOD < U64_MOD.
Proof.
  intros low high Hlow Hhigh.
  replace U64_MOD with (limb_radix U32_MOD 2)
    by (cbv [limb_radix U32_MOD U64_MOD]; reflexivity).
  apply limb_digit_pair_range; try assumption.
  cbv [U32_MOD].
  lia.
Qed.

Lemma u64_list_value_len8_decompose :
  forall xs,
    Zlength xs = 8 ->
    u64_list_value xs =
      u256_of_limbs
        (Znth 0 xs 0) (Znth 1 xs 0)
        (Znth 2 xs 0) (Znth 3 xs 0) +
      u256_of_limbs
        (Znth 4 xs 0) (Znth 5 xs 0)
        (Znth 6 xs 0) (Znth 7 xs 0) * U256_MOD.
Proof.
  intros xs Hlen.
  unfold u64_list_value, limb_list_value.
  rewrite Hlen.
  change
    (@Sum.sum Z (fun i : Z => 0 <= i < 8)
      (ZRange.finite_Z_range 0 8)
      (fun i : Z => Znth i xs 0 * U64_MOD ^ i) =
      u256_of_limbs
        (Znth 0 xs 0) (Znth 1 xs 0)
        (Znth 2 xs 0) (Znth 3 xs 0) +
      u256_of_limbs
        (Znth 4 xs 0) (Znth 5 xs 0)
        (Znth 6 xs 0) (Znth 7 xs 0) * U256_MOD).
  repeat rewrite ZRange.sum_Z_range_cons by lia.
  rewrite ZRange.sum_Z_range_empty by lia.
  cbn.
  cbv [u256_of_limbs U64_MOD U256_MOD].
  ring.
Qed.

Lemma u32_list_value_len16_decompose :
  forall xs,
    Zlength xs = 16 ->
    u32_list_value xs =
      u256_of_limbs
        (Znth 0 xs 0 + Znth 1 xs 0 * U32_MOD)
        (Znth 2 xs 0 + Znth 3 xs 0 * U32_MOD)
        (Znth 4 xs 0 + Znth 5 xs 0 * U32_MOD)
        (Znth 6 xs 0 + Znth 7 xs 0 * U32_MOD) +
      u256_of_limbs
        (Znth 8 xs 0 + Znth 9 xs 0 * U32_MOD)
        (Znth 10 xs 0 + Znth 11 xs 0 * U32_MOD)
        (Znth 12 xs 0 + Znth 13 xs 0 * U32_MOD)
        (Znth 14 xs 0 + Znth 15 xs 0 * U32_MOD) * U256_MOD.
Proof.
  intros xs Hlen.
  unfold u32_list_value, limb_list_value.
  rewrite Hlen.
  change
    (@Sum.sum Z (fun i : Z => 0 <= i < 16)
      (ZRange.finite_Z_range 0 16)
      (fun i : Z => Znth i xs 0 * U32_MOD ^ i) =
      u256_of_limbs
        (Znth 0 xs 0 + Znth 1 xs 0 * U32_MOD)
        (Znth 2 xs 0 + Znth 3 xs 0 * U32_MOD)
        (Znth 4 xs 0 + Znth 5 xs 0 * U32_MOD)
        (Znth 6 xs 0 + Znth 7 xs 0 * U32_MOD) +
      u256_of_limbs
        (Znth 8 xs 0 + Znth 9 xs 0 * U32_MOD)
        (Znth 10 xs 0 + Znth 11 xs 0 * U32_MOD)
        (Znth 12 xs 0 + Znth 13 xs 0 * U32_MOD)
        (Znth 14 xs 0 + Znth 15 xs 0 * U32_MOD) * U256_MOD).
  repeat rewrite ZRange.sum_Z_range_cons by lia.
  rewrite ZRange.sum_Z_range_empty by lia.
  cbn.
  cbv [u256_of_limbs U32_MOD U64_MOD U256_MOD].
  ring.
Qed.

(** * Relations between 32-bit and 64-bit memory views *)

Lemma merge_int64_by_ints_value :
  forall low high value,
    0 <= low < U32_MOD ->
    0 <= high < U32_MOD ->
    0 <= value < U64_MOD ->
    merge_int64_by_ints low high value ->
    value = low + high * U32_MOD.
Proof.
  intros low high value Hlow Hhigh Hvalue Hmerge.
  unfold merge_int64_by_ints in Hmerge.
  destruct Hmerge as
    (b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 &
     Hlow_merge & Hhigh_merge & Hvalue_merge).
  unfold merge_int, merge_int64 in
    Hlow_merge, Hhigh_merge, Hvalue_merge.
  unfold U32_MOD, U64_MOD in *.
  unfold LittleEndian.merge_int in Hlow_merge, Hhigh_merge.
  unfold LittleEndian.merge_int64 in Hvalue_merge.
  rewrite Z.mod_small in Hlow_merge by lia.
  rewrite Z.mod_small in Hhigh_merge by lia.
  rewrite Z.mod_small in Hvalue_merge by lia.
  lia.
Qed.

Lemma store_uint_pair_to_uint64 :
  forall address low high,
    0 <= low < U32_MOD ->
    0 <= high < U32_MOD ->
    store_uint address low ** store_uint (address + 4) high |--
      store_uint64 address (low + high * U32_MOD).
Proof.
  intros address low high Hlow Hhigh.
  unfold store_uint, store_uint64, store_4byte, store_8byte.
  Intros b1 b2 b3 b4.
  Intros b5 b6 b7 b8.
  Exists b1 b2 b3 b4 b5 b6 b7 b8.
  entailer!.
  - replace (address + 4 + 1) with (address + 5) by ring.
    replace (address + 4 + 2) with (address + 6) by ring.
    replace (address + 4 + 3) with (address + 7) by ring.
    entailer!.
  - unfold merge_int in H1, H2.
    unfold merge_int64.
    unfold LittleEndian.merge_int in H1, H2.
    unfold LittleEndian.merge_int64.
    unfold U32_MOD in *.
    rewrite Z.mod_small in H1 by lia.
    rewrite Z.mod_small in H2 by lia.
    rewrite Z.mod_small by (unfold U64_MOD; nia).
    lia.
  - unfold isvalidptr_int64, isvalidptr_int in *.
    destruct H as [[Haddress0 [Haddress3 Halign]] _].
    destruct H0 as [[Haddress4 [Haddress7 Halign4]] _].
    repeat split; try lia.
    exact Halign.
  - unfold Int64.max_unsigned.
    change (low + high * U32_MOD <= U64_MOD - 1).
    rewrite U64_MOD_as_U32_MOD_squared.
    nia.
Qed.

Lemma store_uint_u32_range :
  forall address value,
    store_uint address value |-- “ 0 <= value < U32_MOD ”.
Proof.
  intros address value.
  prop_apply_p (store_uint_range address value).
  Intros.
  dump_pre_spatial.
  unfold U32_MOD.
  destruct H as [Hvalue0 Hvaluemax].
  change (value <= 2 ^ 32 - 1) in Hvaluemax.
  lia.
Qed.

(** * Variable-width 64-bit spatial representation *)

Definition store_u64_limbs (base : addr) (n value : Z) : Assertion :=
  EX xs,
    “ Zlength xs = n /\
       u64_list_bounded xs /\
       u64_list_value xs = value ” &&
    UInt64Array.full base n xs.

Lemma store_u256_limbs_pair_to_store_u64_limbs8 :
  forall base lo hi,
    store_u256_limbs base lo **
    store_u256_limbs (base + (4 * sizeof(UINT64))) hi
    |-- store_u64_limbs base 8 (lo + hi * U256_MOD).
Proof.
  intros base lo hi.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3 x4 x5 x6 x7.
  unfold store_u64_limbs.
  Exists (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil).
  split_pure_spatial.
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    rewrite !sizeof_uint64.
    cbn.
    replace (base + 32 + 0) with (base + 32) by lia.
    replace (base + 32 + 8) with (base + 40) by lia.
    replace (base + 32 + 16) with (base + 48) by lia.
    replace (base + 32 + 24) with (base + 56) by lia.
    entailer!.
  - entailer!.
    + unfold u64_list_bounded, limb_list_bounded.
      intros j Hj.
      apply ZRange.Forall_Znth_Zlength.
      * repeat constructor; tauto.
      * exact Hj.
    + destruct H as [Hx0 [Hx1 [Hx2 [Hx3 Hloeq]]]].
      destruct H0 as [Hx4 [Hx5 [Hx6 [Hx7 Hhieq]]]].
      subst lo hi.
      unfold u64_list_value, limb_list_value.
      change
        (@Sum.sum Z (fun i : Z => 0 <= i < 8)
           (ZRange.finite_Z_range 0 8)
           (fun i : Z =>
              Znth i
                (x0 :: x1 :: x2 :: x3 ::
                 x4 :: x5 :: x6 :: x7 :: nil)
                0 * U64_MOD ^ i) =
         u256_of_limbs x0 x1 x2 x3 +
         u256_of_limbs x4 x5 x6 x7 * U256_MOD).
      repeat rewrite ZRange.sum_Z_range_cons by lia.
      rewrite ZRange.sum_Z_range_empty by lia.
      repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
      cbn.
      cbv [u256_of_limbs U256_MOD U64_MOD].
      ring.
Qed.

Lemma uint64_cells8_to_store_u64_limbs :
  forall base x0 x1 x2 x3 x4 x5 x6 x7,
    0 <= x0 < U64_MOD ->
    0 <= x1 < U64_MOD ->
    0 <= x2 < U64_MOD ->
    0 <= x3 < U64_MOD ->
    0 <= x4 < U64_MOD ->
    0 <= x5 < U64_MOD ->
    0 <= x6 < U64_MOD ->
    0 <= x7 < U64_MOD ->
    ((base + (0 * sizeof(UINT64))) # UInt64 |-> x0) **
    ((base + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
    ((base + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
    ((base + (3 * sizeof(UINT64))) # UInt64 |-> x3) **
    ((base + (4 * sizeof(UINT64))) # UInt64 |-> x4) **
    ((base + (5 * sizeof(UINT64))) # UInt64 |-> x5) **
    ((base + (6 * sizeof(UINT64))) # UInt64 |-> x6) **
    ((base + (7 * sizeof(UINT64))) # UInt64 |-> x7)
    |--
    store_u64_limbs base 8
      (u256_of_limbs x0 x1 x2 x3 +
       u256_of_limbs x4 x5 x6 x7 * U256_MOD).
Proof.
  intros base x0 x1 x2 x3 x4 x5 x6 x7
    Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7.
  unfold store_u64_limbs.
  Exists (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil).
  split_pure_spatial.
  - unfold UInt64Array.full, store_array.
    cbn [store_array_rec].
    entailer!.
  - entailer!.
    + unfold u64_list_bounded, limb_list_bounded.
      intros index Hindex.
      apply ZRange.Forall_Znth_Zlength.
      * repeat constructor; lia.
      * exact Hindex.
    + unfold u64_list_value, limb_list_value.
      change
        (@Sum.sum Z (fun i : Z => 0 <= i < 8)
           (ZRange.finite_Z_range 0 8)
           (fun i : Z =>
              Znth i
                (x0 :: x1 :: x2 :: x3 ::
                 x4 :: x5 :: x6 :: x7 :: nil)
                0 * U64_MOD ^ i) =
         u256_of_limbs x0 x1 x2 x3 +
         u256_of_limbs x4 x5 x6 x7 * U256_MOD).
      repeat rewrite ZRange.sum_Z_range_cons by lia.
      rewrite ZRange.sum_Z_range_empty by lia.
      repeat first [rewrite Znth0_cons | rewrite Znth_cons by lia].
      cbn.
      cbv [u256_of_limbs U256_MOD U64_MOD].
      ring.
Qed.

(** Forget the values of nine materialized limbs while retaining ownership. *)
Lemma uint64_cells9_to_full_shape :
  forall base x0 x1 x2 x3 x4 x5 x6 x7 x8,
    ((base + (0 * sizeof(UINT64))) # UInt64 |-> x0) **
    ((base + (1 * sizeof(UINT64))) # UInt64 |-> x1) **
    ((base + (2 * sizeof(UINT64))) # UInt64 |-> x2) **
    ((base + (3 * sizeof(UINT64))) # UInt64 |-> x3) **
    ((base + (4 * sizeof(UINT64))) # UInt64 |-> x4) **
    ((base + (5 * sizeof(UINT64))) # UInt64 |-> x5) **
    ((base + (6 * sizeof(UINT64))) # UInt64 |-> x6) **
    ((base + (7 * sizeof(UINT64))) # UInt64 |-> x7) **
    ((base + (8 * sizeof(UINT64))) # UInt64 |-> x8)
    |-- UInt64Array.full_shape base 9.
Proof.
  intros.
  unfold UInt64Array.full_shape, store_undef_array.
  cbn [store_undef_array_rec Z.to_nat].
  cbv [Pos.to_nat Pos.iter_op Nat.add].
  cbn [store_undef_array_rec].
  Exists x0 x1 x2 x3 x4 x5 x6 x7 x8.
  rewrite !sizeof_uint64.
  cbn.
  entailer!.
Qed.

(** * SM2 field-modulus representation *)

Definition SM2_P_Z : Z :=
  2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1.

(** Canonical Montgomery representation modulo the SM2 field prime. *)
Definition mont_p (x : Z) : Z :=
  Montgomery.mont SM2_P_Z U256_MOD x.

Lemma sm2_p_montgomery_bounds :
  0 < SM2_P_Z < U256_MOD /\
  U256_MOD < 2 * SM2_P_Z.
Proof.
  cbv [SM2_P_Z U256_MOD].
  lia.
Qed.

Lemma mont_p_range :
  forall x, 0 <= mont_p x < SM2_P_Z.
Proof.
  intros x.
  unfold mont_p.
  apply Montgomery.mont_range.
  exact (proj1 (proj1 sm2_p_montgomery_bounds)).
Qed.

Lemma sm2_p_radix_rel_prime :
  rel_prime SM2_P_Z U256_MOD.
Proof.
  apply (proj1 (Zgcd_1_rel_prime _ _)).
  vm_compute.
  reflexivity.
Qed.

Lemma mont_p_injective :
  forall x y,
    0 <= x < SM2_P_Z ->
    0 <= y < SM2_P_Z ->
    mont_p x = mont_p y ->
    x = y.
Proof.
  intros x y Hx Hy Hequal.
  unfold mont_p in Hequal.
  apply (Montgomery.mont_injective_canonical
    SM2_P_Z U256_MOD x y).
  - exact (proj1 (proj1 sm2_p_montgomery_bounds)).
  - exact sm2_p_radix_rel_prime.
  - exact Hx.
  - exact Hy.
  - exact Hequal.
Qed.

Lemma mont_p_zero :
  mont_p 0 = 0.
Proof.
  unfold mont_p.
  apply Montgomery.mont_zero.
  pose proof sm2_p_montgomery_bounds.
  lia.
Qed.

Lemma mont_p_eq_zero_iff :
  forall x,
    0 <= x < SM2_P_Z ->
    (mont_p x = 0 <-> x = 0).
Proof.
  intros x Hx.
  split.
  - intros Hzero.
    apply (mont_p_injective x 0).
    + exact Hx.
    + pose proof sm2_p_montgomery_bounds. lia.
    + rewrite mont_p_zero. exact Hzero.
  - intros. subst x. exact mont_p_zero.
Qed.

Lemma mont_p_neg_mod :
  forall x,
    mont_p ((-x) mod SM2_P_Z) = (- mont_p x) mod SM2_P_Z.
Proof.
  intros x.
  unfold mont_p.
  rewrite Montgomery.mont_mod
    by (pose proof sm2_p_montgomery_bounds; lia).
  apply Montgomery.mont_neg.
  pose proof sm2_p_montgomery_bounds.
  lia.
Qed.

Definition SM2_P_LIMB_0 : Z := U64_MOD - 1.
Definition SM2_P_LIMB_1 : Z := U64_MOD - U32_MOD.
Definition SM2_P_LIMB_2 : Z := U64_MOD - 1.
Definition SM2_P_LIMB_3 : Z := U64_MOD - U32_MOD - 1.

Lemma sm2_p_limbs :
  0 <= SM2_P_LIMB_0 < U64_MOD /\
  0 <= SM2_P_LIMB_1 < U64_MOD /\
  0 <= SM2_P_LIMB_2 < U64_MOD /\
  0 <= SM2_P_LIMB_3 < U64_MOD /\
  SM2_P_Z =
    u256_of_limbs
      SM2_P_LIMB_0 SM2_P_LIMB_1 SM2_P_LIMB_2 SM2_P_LIMB_3.
Proof.
  vm_compute.
  repeat split; congruence.
Qed.

Definition store_sm2_p : Assertion :=
  store_u256_limbs (&((&("SM2_P")) ->ₛ "v")) SM2_P_Z.

Definition SM2_RHOP_Z : Z := U256_MOD - SM2_P_Z.

Definition SM2_RHOP0_Z : Z := 1.
Definition SM2_RHOP1_Z : Z := U32_MOD - 1.
Definition SM2_RHOP2_Z : Z := 0.
Definition SM2_RHOP3_Z : Z := U32_MOD.

Lemma sm2_rhop_limbs :
  0 <= SM2_RHOP0_Z < U64_MOD /\
  0 <= SM2_RHOP1_Z < U64_MOD /\
  0 <= SM2_RHOP2_Z < U64_MOD /\
  0 <= SM2_RHOP3_Z < U64_MOD /\
  SM2_RHOP_Z =
    u256_of_limbs
      SM2_RHOP0_Z SM2_RHOP1_Z SM2_RHOP2_Z SM2_RHOP3_Z.
Proof.
  vm_compute.
  repeat split; congruence.
Qed.

Definition store_sm2_rhop : Assertion :=
  store_u256_limbs (&((&("SM2_rhoP")) ->ₛ "v")) SM2_RHOP_Z.

(** [SM2_H] is R^2 mod P for R = 2^256. *)
Definition SM2_H0_Z : Z := 8589934595.
Definition SM2_H1_Z : Z := 12884901887.
Definition SM2_H2_Z : Z := 4294967297.
Definition SM2_H3_Z : Z := 17179869186.

Definition SM2_H_Z : Z :=
  u256_of_limbs SM2_H0_Z SM2_H1_Z SM2_H2_Z SM2_H3_Z.

Definition SM2_H_LIMBS : list Z :=
  [SM2_H0_Z; SM2_H1_Z; SM2_H2_Z; SM2_H3_Z].

Definition store_sm2_h : Assertion :=
  store_u256_limbs (&((&("SM2_H")) ->ₛ "v")) SM2_H_Z.

Lemma sm2_h_limbs :
  0 <= SM2_H0_Z < U64_MOD /\
  0 <= SM2_H1_Z < U64_MOD /\
  0 <= SM2_H2_Z < U64_MOD /\
  0 <= SM2_H3_Z < U64_MOD /\
  SM2_H_Z =
    u256_of_limbs SM2_H0_Z SM2_H1_Z SM2_H2_Z SM2_H3_Z.
Proof.
  vm_compute.
  repeat split; congruence.
Qed.

Lemma sm2_h_is_r2 :
  SM2_H_Z = (U256_MOD * U256_MOD) mod SM2_P_Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sm2_h_bounds :
  0 <= SM2_H_Z < SM2_P_Z.
Proof.
  rewrite sm2_h_is_r2.
  apply Z.mod_pos_bound.
  cbv [SM2_P_Z].
  lia.
Qed.

Definition store_fp (address : addr) (x : Z) : Assertion :=
  store_mod SM2_P_Z address x.

Lemma store_fp_base0_pack :
  forall address x,
    0 <= x < SM2_P_Z ->
    store_u256_limbs
      (&((address) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) x
    |-- store_fp address x.
Proof.
  intros address x Hx.
  unfold store_fp.
  exact (store_mod_base0_pack SM2_P_Z address x Hx).
Qed.

Lemma store_fp_base0_unpack :
  forall address x,
    store_fp address x |--
    “ 0 <= x < SM2_P_Z ” &&
    store_u256_limbs
      (&((address) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) x.
Proof.
  intros address x.
  unfold store_fp.
  exact (store_mod_base0_unpack SM2_P_Z address x).
Qed.

(** Materialize a canonical field element as the exact four-limb array used
    by whole-record C assignments.  This bridge is deliberately invoked only
    by named materialization strategies. *)
Lemma store_fp_materialize_full :
  forall address x,
    store_fp address x |--
      EX xs,
        “ 0 <= x < SM2_P_Z /\
          Zlength xs = 4 /\
          u64_list_bounded xs /\
          u64_list_value xs = x ” &&
        UInt64Array.full (&((address) # "u32" ->ₛ "v")) 4 xs.
Proof.
  intros address x.
  unfold store_fp, store_mod, store_u256, store_u256_limbs.
  Intros x0 x1 x2 x3.
  Exists [x0; x1; x2; x3].
  assert (Hbounded : u64_list_bounded [x0; x1; x2; x3]).
  {
    unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    repeat split; try tauto.
    all: rewrite Zlength_nil in H1; lia.
  }
  rewrite u64_list_value_four.
  unfold UInt64Array.full, store_array.
  cbn [store_array_rec].
  entailer!.
Qed.

(** * SM2 group-order representation *)

(** SM2 group order:
    FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123. *)
Definition SM2_N0_Z : Z := 6033684446255071523.
Definition SM2_N1_Z : Z := 8215655796475036971.
Definition SM2_N2_Z : Z := U64_MOD - 1.
Definition SM2_N3_Z : Z := U64_MOD - U32_MOD - 1.

Definition SM2_N_Z : Z :=
  u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.

(** Canonical Montgomery representation modulo the SM2 group order. *)
Definition mont_n (x : Z) : Z :=
  Montgomery.mont SM2_N_Z U256_MOD x.

Definition SM2_N_LIMBS : list Z :=
  [SM2_N0_Z; SM2_N1_Z; SM2_N2_Z; SM2_N3_Z].

(** [SM2_rhoN] is 2^256 - SM2_N, used as -N modulo 2^256. *)
Definition SM2_RHON0_Z : Z := 12413059627454480093.
Definition SM2_RHON1_Z : Z := 10231088277234514644.
Definition SM2_RHON2_Z : Z := 0.
Definition SM2_RHON3_Z : Z := U32_MOD.

Definition SM2_RHON_Z : Z := U256_MOD - SM2_N_Z.

Definition SM2_RHON_LIMBS : list Z :=
  [SM2_RHON0_Z; SM2_RHON1_Z; SM2_RHON2_Z; SM2_RHON3_Z].

(** [SM2_NH] is R^2 mod N for R = 2^256. *)
Definition SM2_NH0_Z : Z := 10381239898464145184.
Definition SM2_NH1_Z : Z := 3775230670132978426.
Definition SM2_NH2_Z : Z := 7066086570100515028.
Definition SM2_NH3_Z : Z := 2212925560603753787.

Definition SM2_NH_Z : Z :=
  u256_of_limbs SM2_NH0_Z SM2_NH1_Z SM2_NH2_Z SM2_NH3_Z.

Definition SM2_NH_LIMBS : list Z :=
  [SM2_NH0_Z; SM2_NH1_Z; SM2_NH2_Z; SM2_NH3_Z].

(** -N^{-1} modulo 2^64, as used by Montgomery reduction. *)
Definition SM2_NEG_INV_N : Z := 3638801332807469429.

(** Exact quotient witnessing the low-word negative-inverse equation. *)
Definition SM2_NEG_INV_N_QUOTIENT : Z := 1190203480735857098.

Definition store_sm2_n : Assertion :=
  store_u256_limbs (&((&("SM2_N")) ->ₛ "v")) SM2_N_Z.

Definition store_sm2_rhon : Assertion :=
  store_u256_limbs (&((&("SM2_rhoN")) ->ₛ "v")) SM2_RHON_Z.

Definition store_sm2_nh : Assertion :=
  store_u256_limbs (&((&("SM2_NH")) ->ₛ "v")) SM2_NH_Z.

Definition store_sm2_neg_inv_n : Assertion :=
  (&("SM2_neg_invN")) # UInt64 |-> SM2_NEG_INV_N.

Definition store_fn (address : addr) (x : Z) : Assertion :=
  store_mod SM2_N_Z address x.

Lemma store_fn_base0_pack :
  forall address x,
    0 <= x < SM2_N_Z ->
    store_u256_limbs
      (&((address) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) x
    |-- store_fn address x.
Proof.
  intros address x Hx.
  unfold store_fn.
  exact (store_mod_base0_pack SM2_N_Z address x Hx).
Qed.

Lemma store_fn_base0_unpack :
  forall address x,
    store_fn address x |--
    “ 0 <= x < SM2_N_Z ” &&
    store_u256_limbs
      (&((address) # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) x.
Proof.
  intros address x.
  unfold store_fn.
  exact (store_mod_base0_unpack SM2_N_Z address x).
Qed.

Lemma sm2_n_limbs :
    0 <= SM2_N0_Z < U64_MOD /\
    0 <= SM2_N1_Z < U64_MOD /\
    0 <= SM2_N2_Z < U64_MOD /\
    0 <= SM2_N3_Z < U64_MOD.
Proof.
  vm_compute.
  repeat split; congruence.
Qed.

Lemma sm2_n_limbs_exact :
    0 <= SM2_N0_Z < U64_MOD /\
    0 <= SM2_N1_Z < U64_MOD /\
    0 <= SM2_N2_Z < U64_MOD /\
    0 <= SM2_N3_Z < U64_MOD /\
    SM2_N_Z =
      u256_of_limbs SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z.
Proof.
  pose proof sm2_n_limbs as [H0 [H1 [H2 H3]]].
  repeat split; try lia.
Qed.

Lemma sm2_n_bounds :
  0 < SM2_N_Z < U256_MOD.
Proof.
  cbv [SM2_N_Z SM2_N0_Z SM2_N1_Z SM2_N2_Z SM2_N3_Z
       u256_of_limbs U32_MOD U64_MOD U256_MOD].
  lia.
Qed.

Lemma mont_n_range :
  forall x, 0 <= mont_n x < SM2_N_Z.
Proof.
  intros x.
  unfold mont_n.
  apply Montgomery.mont_range.
  exact (proj1 sm2_n_bounds).
Qed.

Lemma sm2_rhon_limbs :
  SM2_RHON_Z =
    u256_of_limbs
      SM2_RHON0_Z
      SM2_RHON1_Z
      SM2_RHON2_Z
      SM2_RHON3_Z /\
  0 <= SM2_RHON0_Z < U64_MOD /\
  0 <= SM2_RHON1_Z < U64_MOD /\
  0 <= SM2_RHON2_Z < U64_MOD /\
  0 <= SM2_RHON3_Z < U64_MOD.
Proof.
  vm_compute.
  repeat split; congruence.
Qed.

Lemma sm2_rhon_is_neg_n :
  SM2_N_Z + SM2_RHON_Z = U256_MOD.
Proof.
  unfold SM2_RHON_Z.
  pose proof sm2_n_bounds.
  lia.
Qed.

Lemma sm2_nh_limbs :
    0 <= SM2_NH0_Z < U64_MOD /\
    0 <= SM2_NH1_Z < U64_MOD /\
    0 <= SM2_NH2_Z < U64_MOD /\
    0 <= SM2_NH3_Z < U64_MOD /\
    SM2_NH_Z =
      u256_of_limbs SM2_NH0_Z SM2_NH1_Z SM2_NH2_Z SM2_NH3_Z.
Proof.
  vm_compute.
  repeat split; congruence.
Qed.

Lemma sm2_nh_is_r2 :
  SM2_NH_Z = (U256_MOD * U256_MOD) mod SM2_N_Z.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sm2_nh_bounds :
  0 <= SM2_NH_Z < SM2_N_Z.
Proof.
  rewrite sm2_nh_is_r2.
  apply Z.mod_pos_bound.
  pose proof sm2_n_bounds.
  lia.
Qed.

Lemma sm2_neg_inv_n_correct :
  (SM2_N_Z * SM2_NEG_INV_N) mod U64_MOD = U64_MOD - 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma sm2_neg_inv_n0_multiple :
  SM2_N0_Z * SM2_NEG_INV_N + 1 =
  SM2_NEG_INV_N_QUOTIENT * U64_MOD.
Proof.
  vm_compute.
  reflexivity.
Qed.
