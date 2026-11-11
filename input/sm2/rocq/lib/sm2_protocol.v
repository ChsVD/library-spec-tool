(** SM2 key, digest, signature, and protocol-level memory semantics. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Export
  sm2_protocol_def byte_encoding sm3 sm3_def ecc
  sm2_primality sm2_generator_order sm2_ecc_const_table
  sm2_basepoint_mul.

Import ListNotations.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

Definition valid_sm2_private_key (private_key : Z) : Prop :=
  1 <= private_key < SM2_N_Z - 1.

Definition valid_sm2_keypair
    (private_key : Z) (public_key : ec_point) : Prop :=
  valid_sm2_private_key private_key /\
  public_key = sm2_point_mul private_key SM2_G_POINT.

Definition valid_sm2_public_key (public_key : ec_point) : Prop :=
  exists private_key,
    valid_sm2_keypair private_key public_key.

Definition sm2_id_digest_output_aligned
    (result id_len : Z) : Prop :=
  id_len > 50 \/ aligned_4 result.

Definition sm2_message_input_aligned
    (message message_len : Z) : Prop :=
  message_len < 96 \/ aligned_4 message.

Lemma sm2_id_digest_output_aligned_success :
  forall result id_len,
    sm2_id_digest_output_aligned result id_len ->
    id_len <= 50 ->
    aligned_4 result.
Proof.
  intros result id_len Haligned Hlength.
  unfold sm2_id_digest_output_aligned in Haligned.
  destruct Haligned; [lia | assumption].
Qed.

Lemma sm2_message_input_aligned_update :
  forall message message_len,
    sm2_message_input_aligned message message_len ->
    sm3_update_data_aligned message message_len 32.
Proof.
  intros message message_len Haligned.
  apply sm3_update_data_aligned_after_32.
  exact Haligned.
Qed.

Definition sm2_point_x (point : ec_point) : Z :=
  match point with
  | SMain.inf_elt _ _ _ _ _ => 0
  | @SMain.curve_elt _ _ _ _ _ _ point_x _ _ =>
      sm2_fe_value point_x
  end.

Definition sm2_point_y (point : ec_point) : Z :=
  match point with
  | SMain.inf_elt _ _ _ _ _ => 0
  | @SMain.curve_elt _ _ _ _ _ _ _ point_y _ =>
      sm2_fe_value point_y
  end.

Definition sm2_entla_bytes (id_len : Z) : list Z :=
  [((8 * id_len) / SM2_BYTE_BASE) mod SM2_BYTE_BASE;
   (8 * id_len) mod SM2_BYTE_BASE].

Definition sm2_za_input
    (id : list Z) (public_key : ec_point) : list Z :=
  sm2_entla_bytes (Zlength id) ++ id ++
  u256_to_be_bytes SM2_A_Z ++
  u256_to_be_bytes SM2_B_Z ++
  u256_to_be_bytes SM2_G_X_Z ++
  u256_to_be_bytes SM2_G_Y_Z ++
  u256_to_be_bytes (sm2_point_x public_key) ++
  u256_to_be_bytes (sm2_point_y public_key).

Lemma sm2_point_x_bounds :
  forall point,
    0 <= sm2_point_x point < SM2_P_Z.
Proof.
  intros point.
  destruct point as [|point_x point_y Hcurve].
  - cbn [sm2_point_x].
    pose proof sm2_p_gt_one. lia.
  - cbn [sm2_point_x].
    apply sm2_fe_value_bounds.
Qed.

Lemma sm2_point_y_bounds :
  forall point,
    0 <= sm2_point_y point < SM2_P_Z.
Proof.
  intros point.
  destruct point as [|point_x point_y Hcurve].
  - cbn [sm2_point_y].
    pose proof sm2_p_gt_one. lia.
  - cbn [sm2_point_y].
    apply sm2_fe_value_bounds.
Qed.

Lemma sm2_generator_point_coordinates :
  sm2_point_x SM2_G_POINT = SM2_G_X_Z /\
  sm2_point_y SM2_G_POINT = SM2_G_Y_Z.
Proof. split; reflexivity. Qed.

Lemma sm2_entla_bytes_length :
  forall id_len,
    Zlength (sm2_entla_bytes id_len) = 2.
Proof. intros; reflexivity. Qed.

Lemma sm2_entla_bytes_bounded :
  forall id_len,
    u8_list_bounded (sm2_entla_bytes id_len).
Proof.
  intros id_len.
  unfold sm2_entla_bytes, u8_list_bounded, limb_list_bounded.
  intros index Hindex.
  rewrite !Zlength_cons, Zlength_nil in Hindex.
  assert (index = 0 \/ index = 1) by lia.
  destruct H as [-> | ->]; cbn [Znth].
  - apply Z.mod_pos_bound. unfold SM2_BYTE_BASE; lia.
  - apply Z.mod_pos_bound. unfold SM2_BYTE_BASE; lia.
Qed.

Lemma sm2_za_input_length :
  forall id public_key,
    Zlength (sm2_za_input id public_key) =
      2 + Zlength id + 192.
Proof.
  intros id public_key.
  unfold sm2_za_input.
  repeat rewrite Zlength_app.
  rewrite sm2_entla_bytes_length.
  repeat rewrite u256_to_be_bytes_length.
  lia.
Qed.

Lemma sm2_za_input_bounded :
  forall id public_key,
    u8_list_bounded id ->
    u8_list_bounded (sm2_za_input id public_key).
Proof.
  intros id public_key Hid.
  unfold sm2_za_input, u8_list_bounded.
  rewrite !limb_list_bounded_app.
  split. { apply sm2_entla_bytes_bounded. }
  split. { exact Hid. }
  split.
  { apply u256_to_be_bytes_bounded. exact (proj1 sm2_a_bounds). }
  split.
  { apply u256_to_be_bytes_bounded. exact (proj1 sm2_b_bounds). }
  split.
  - apply u256_to_be_bytes_bounded.
    rewrite <- (proj1 sm2_generator_point_coordinates).
    exact (proj1 (sm2_point_x_bounds SM2_G_POINT)).
  - split.
    {
      apply u256_to_be_bytes_bounded.
      rewrite <- (proj2 sm2_generator_point_coordinates).
      exact (proj1 (sm2_point_y_bounds SM2_G_POINT)).
    }
    split.
    {
      apply u256_to_be_bytes_bounded.
      exact (proj1 (sm2_point_x_bounds public_key)).
    }
    apply u256_to_be_bytes_bounded.
    exact (proj1 (sm2_point_y_bounds public_key)).
Qed.

Definition sm2_za_digest
    (id : list Z) (public_key : ec_point) : list Z :=
  sm3_digest_bytes (sm2_za_input id public_key).

Definition sm2_message_digest
    (id : list Z) (public_key : ec_point)
    (message : list Z) : list Z :=
  sm3_digest_bytes (sm2_za_digest id public_key ++ message).

Definition sm2_signature_generated
    (digest private_key r s : Z) : Prop :=
  valid_sm2_private_key private_key /\
  exists nonce x y inverse,
    1 <= nonce < SM2_N_Z /\
    afpoint_represents
      x y (sm2_point_mul nonce SM2_G_POINT) /\
    0 <= inverse < SM2_N_Z /\
    ((1 + private_key) * inverse) mod SM2_N_Z = 1 /\
    r = (digest + x) mod SM2_N_Z /\
    1 <= r < SM2_N_Z /\
    (r + nonce) mod SM2_N_Z <> 0 /\
    s = ((nonce - r * private_key) * inverse) mod SM2_N_Z /\
    1 <= s < SM2_N_Z.

Definition sm2_signature_verifies
    (digest : Z) (public_key : ec_point) (r s : Z) : Prop :=
  1 <= r < SM2_N_Z /\
  1 <= s < SM2_N_Z /\
  let t := (r + s) mod SM2_N_Z in
  t <> 0 /\
  let result :=
    sm2_point_add
      (sm2_point_mul s SM2_G_POINT)
      (sm2_point_mul t public_key) in
  result <> ECInfinity /\
  exists x y,
    afpoint_represents x y result /\
    r = (digest + x) mod SM2_N_Z.

Definition undef_sm2_private_key (address : addr) : Assertion :=
  UndefStructPredu32 (&(address # "PrivKey" ->ₛ "da")).

Definition store_sm2_private_key
    (address : addr) (private_key : Z) : Assertion :=
  “ valid_sm2_private_key private_key ” &&
  store_fn (&(address # "PrivKey" ->ₛ "da")) private_key.

Definition undef_sm2_signature (address : addr) : Assertion :=
  UndefStructPredu32 (&(address # "SM2SIG" ->ₛ "r")) **
  UndefStructPredu32 (&(address # "SM2SIG" ->ₛ "s")).

Definition store_sm2_signature
    (address : addr) (r s : Z) : Assertion :=
  store_u256 (&(address # "SM2SIG" ->ₛ "r")) r **
  store_u256 (&(address # "SM2SIG" ->ₛ "s")) s.

Definition store_sm2_public_key
    (address : addr) (public_key : ec_point) : Assertion :=
  “ valid_sm2_public_key public_key ” &&
  store_afpoint address public_key.

Definition store_sm2_za
    (address : addr) (id : list Z) (public_key : ec_point)
    (za : list Z) : Assertion :=
  “ za = sm2_za_digest id public_key ” &&
  byte_encoding.store_bytes address 32 za.

Definition store_sm2_g : Assertion :=
  store_afpoint (&("SM2_G")) SM2_G_POINT.

Definition store_sm2_get_public_key_globals : Assertion :=
  store_sm2_base_point_table **
  store_sm2_p ** store_sm2_rhop **
  store_jpoint_zero ** store_sm2_inv2p.

Definition store_sm2_keypair_globals : Assertion :=
  store_sm2_n ** store_sm2_rhon **
  store_sm2_get_public_key_globals.

Definition store_sm2_za_globals : Assertion :=
  store_sm2_a ** store_sm2_b ** store_sm2_g ** store_sm3_ti.

Definition store_sm2_sign_dgst_globals : Assertion :=
  store_sm2_n ** store_sm2_rhon ** store_sm2_nh **
  store_sm2_neg_inv_n **
  store_sm2_mont_base_point_table **
  store_sm2_p ** store_sm2_rhop **
  store_bn_zero ** store_montg_one.

Definition store_sm2_sign_globals : Assertion :=
  store_sm2_za_globals ** store_sm2_sign_dgst_globals.

Definition store_sm2_verify_dgst_globals : Assertion :=
  store_sm2_a ** store_sm2_b **
  store_sm2_n ** store_sm2_rhon **
  store_sm2_h ** store_sm2_p ** store_sm2_rhop **
  store_sm2_mont_base_point_table **
  store_jpoint_zero ** store_bn_zero ** store_montg_one.

Lemma sm2_verify_dgst_return_resources_fold :
  forall pubkey dgst signature s r public_key digest_bytes xs ys zs,
    u64_list_value xs = 1 ->
    u64_list_value ys = 1 ->
    u64_list_value zs = 0 ->
    store_u256 (&(signature # "SM2SIG" ->ₛ "r")) r **
    (store_sm2_n **
     (store_sm2_rhon **
      (store_bn_zero **
       (store_montg_one **
        (store_sm2_p **
         (store_sm2_rhop **
          (store_afpoint pubkey public_key **
           (store_sm2_h **
            (store_fn (&(signature # "SM2SIG" ->ₛ "s")) s **
             (store_sm2_mont_base_point_table **
              (byte_encoding.store_bytes dgst 32 digest_bytes **
               (store_sm2_a **
                (store_sm2_b **
                 (UInt64Array.full
                    &((&("JPoint_ZERO")) ->ₛ "z" .ₛ "v") 4 zs **
                  (UInt64Array.full
                     &((&("JPoint_ZERO")) ->ₛ "y" .ₛ "v") 4 ys **
                   UInt64Array.full
                     &((&("JPoint_ZERO")) ->ₛ "x" .ₛ "v") 4 xs)))))))))))))))
    |-- store_sm2_signature signature r s **
        (byte_encoding.store_bytes dgst 32 digest_bytes **
         (store_afpoint pubkey public_key ** store_sm2_verify_dgst_globals)).
Proof.
  intros pubkey dgst signature s r public_key digest_bytes xs ys zs
    Hx Hy Hz.
  sep_apply_l_atomic
    (store_fn_base0_unpack (&(signature # "SM2SIG" ->ₛ "s")) s).
  unfold store_sm2_signature, store_u256,
    store_sm2_verify_dgst_globals.
  Intros.
  rewrite Z.mul_0_l, Z.add_0_r.
  cancel.
  sep_apply_l_atomic (jpoint_zero_arrays_fold xs ys zs Hx Hy Hz).
  reflexivity.
Qed.

Lemma sm2_verify_dgst_checked_return_resources_fold :
  forall pubkey dgst signature s r public_key digest_bytes xs ys zs,
    u64_list_value xs = 1 ->
    u64_list_value ys = 1 ->
    u64_list_value zs = 0 ->
    store_bn_zero **
    (store_sm2_p **
     (store_sm2_rhop **
      (store_afpoint pubkey public_key **
       (store_sm2_h **
        (store_montg_one **
         (store_fn (&(signature # "SM2SIG" ->ₛ "s")) s **
          (store_sm2_mont_base_point_table **
           (byte_encoding.store_bytes dgst 32 digest_bytes **
            (store_fn (&(signature # "SM2SIG" ->ₛ "r")) r **
             (store_sm2_n **
              (store_sm2_a **
               (store_sm2_b **
                (UInt64Array.full
                   &((&("JPoint_ZERO")) ->ₛ "z" .ₛ "v") 4 zs **
                 (UInt64Array.full
                    &((&("JPoint_ZERO")) ->ₛ "y" .ₛ "v") 4 ys **
                  (UInt64Array.full
                     &((&("JPoint_ZERO")) ->ₛ "x" .ₛ "v") 4 xs **
                   store_sm2_rhon)))))))))))))))
    |-- store_sm2_signature signature r s **
        (byte_encoding.store_bytes dgst 32 digest_bytes **
         (store_afpoint pubkey public_key ** store_sm2_verify_dgst_globals)).
Proof.
  intros pubkey dgst signature s r public_key digest_bytes xs ys zs
    Hx Hy Hz.
  sep_apply_l_atomic
    (store_fn_base0_unpack (&(signature # "SM2SIG" ->ₛ "s")) s).
  sep_apply_l_atomic
    (store_fn_base0_unpack (&(signature # "SM2SIG" ->ₛ "r")) r).
  unfold store_sm2_signature, store_u256,
    store_sm2_verify_dgst_globals.
  Intros.
  Intros.
  repeat rewrite Z.mul_0_l, Z.add_0_r.
  cancel.
  sep_apply_l_atomic (jpoint_zero_arrays_fold xs ys zs Hx Hy Hz).
  rewrite Z.add_0_r.
  cancel.
Qed.

Lemma sm2_verify_dgst_early_return_resources_fold :
  forall pubkey dgst signature s r public_key digest_bytes xs ys zs x y,
    afpoint_represents x y public_key ->
    u64_list_value xs = 1 ->
    u64_list_value ys = 1 ->
    u64_list_value zs = 0 ->
    store_u256 (&(signature # "SM2SIG" ->ₛ "s")) s **
    (store_u256 (&("SM2_N"))
       (u64_list_value
          (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil)) **
     (store_u256 (&(signature # "SM2SIG" ->ₛ "r")) r **
      (store_afpoint_fields pubkey x y **
       (store_sm2_a **
        (store_sm2_b **
         (store_sm2_p **
          (store_sm2_rhop **
           (UInt64Array.full
              &((&("JPoint_ZERO")) ->ₛ "z" .ₛ "v") 4 zs **
            (UInt64Array.full
               &((&("JPoint_ZERO")) ->ₛ "y" .ₛ "v") 4 ys **
             (UInt64Array.full
                &((&("JPoint_ZERO")) ->ₛ "x" .ₛ "v") 4 xs **
              (store_montg_one **
               (store_bn_zero **
                (store_sm2_mont_base_point_table **
                 (store_sm2_h **
                  (store_sm2_rhon **
                   byte_encoding.store_bytes dgst 32 digest_bytes)))))))))))))))
    |-- store_sm2_signature signature r s **
        (byte_encoding.store_bytes dgst 32 digest_bytes **
         (store_afpoint pubkey public_key ** store_sm2_verify_dgst_globals)).
Proof.
  intros pubkey dgst signature s r public_key digest_bytes xs ys zs x y
    Hpoint Hx Hy Hz.
  assert (HN :
    u64_list_value
      (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) =
    SM2_N_Z).
  {
    rewrite u64_list_value_four.
    destruct sm2_n_limbs_exact as [_ [_ [_ [_ HN]]]].
    symmetry; exact HN.
  }
  rewrite HN.
  unfold store_sm2_signature, store_sm2_verify_dgst_globals,
    store_sm2_n, store_u256, store_afpoint.
  Exists x y.
  split_pure_spatial.
  - rewrite <- (global_u32_v_addr_eq "SM2_N").
    sep_apply_l_atomic (jpoint_zero_arrays_fold xs ys zs Hx Hy Hz).
    cancel.
  - dump_pre_spatial.
    exact Hpoint.
Qed.

Definition store_sm2_verify_globals : Assertion :=
  store_sm2_verify_dgst_globals ** store_sm2_g ** store_sm3_ti.

Lemma valid_sm2_private_key_bounds :
  forall private_key,
    valid_sm2_private_key private_key ->
    0 < private_key < SM2_N_Z.
Proof.
  intros private_key Hvalid.
  unfold valid_sm2_private_key in Hvalid.
  lia.
Qed.

Lemma valid_sm2_private_key_from_rejection_checks :
  forall private_key private_key_plus_one,
    0 <= private_key < SM2_N_Z ->
    private_key <> 0 ->
    private_key_plus_one = (private_key + 1) mod SM2_N_Z ->
    private_key_plus_one <> 0 ->
    valid_sm2_private_key private_key.
Proof.
  intros private_key private_key_plus_one
    Hprivate_key Hnonzero Hplus_one Hplus_one_nonzero.
  unfold valid_sm2_private_key.
  assert (Hnot_upper : private_key <> SM2_N_Z - 1).
  {
    intros Heq.
    subst private_key.
    replace (SM2_N_Z - 1 + 1) with SM2_N_Z in Hplus_one by ring.
    rewrite Z.mod_same in Hplus_one by
      (pose proof sm2_n_bounds; lia).
    exact (Hplus_one_nonzero Hplus_one).
  }
  lia.
Qed.

Lemma sm2_n_mod_eq_of_divide :
  forall left right,
    0 <= right < SM2_N_Z ->
    (SM2_N_Z | left - right) ->
    left mod SM2_N_Z = right.
Proof.
  intros left right Hright [quotient Hquotient].
  pose proof sm2_n_bounds.
  replace left with (right + quotient * SM2_N_Z) by nia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small.
  exact Hright.
Qed.

Lemma sm2_n_mod_inverse_exists :
  forall value,
    0 < value < SM2_N_Z ->
    exists inverse,
      0 <= inverse < SM2_N_Z /\
      (value * inverse) mod SM2_N_Z = 1.
Proof.
  intros value Hvalue.
  assert (Hrel : rel_prime value SM2_N_Z).
  {
    apply (proj1 (Zgcd_1_rel_prime _ _)).
    apply sm2_n_nonzero_gcd_one; lia.
  }
  destruct (rel_prime_bezout value SM2_N_Z Hrel)
    as [u v Hbezout].
  exists (u mod SM2_N_Z).
  split.
  - apply Z.mod_pos_bound.
    pose proof sm2_n_bounds. lia.
  - apply sm2_n_mod_eq_of_divide.
    + pose proof sm2_n_bounds. lia.
    + pose proof (Z.div_mod u SM2_N_Z ltac:(pose proof sm2_n_bounds; lia))
        as Hu.
      exists (-(value * (u / SM2_N_Z) + v)).
      nia.
Qed.

Lemma sm2_point_mul_infinity :
  forall scalar,
    0 <= scalar ->
    sm2_point_mul scalar ECInfinity = ECInfinity.
Proof.
  intros scalar Hscalar.
  unfold sm2_point_mul.
  rewrite <- sm2_group_identity.
  apply EGroup.gpow_e.
  exact Hscalar.
Qed.

Lemma sm2_generator_mul_mod :
  forall scalar,
    0 <= scalar ->
    sm2_point_mul (scalar mod SM2_N_Z) SM2_G_POINT =
    sm2_point_mul scalar SM2_G_POINT.
Proof.
  intros scalar Hscalar.
  pose proof sm2_n_bounds as Hn.
  assert (Hquotient : 0 <= scalar / SM2_N_Z).
  { apply Z.div_pos; lia. }
  assert (Hremainder : 0 <= scalar mod SM2_N_Z).
  { apply Z.mod_pos_bound; lia. }
  replace scalar with
    (SM2_N_Z * (scalar / SM2_N_Z) + scalar mod SM2_N_Z)
    at 2
    by (pose proof (Z.div_mod scalar SM2_N_Z ltac:(lia)); lia).
  rewrite sm2_point_mul_add by lia.
  rewrite sm2_point_mul_mul by lia.
  rewrite sm2_generator_mul_order.
  rewrite sm2_point_mul_infinity by lia.
  rewrite sm2_point_add_infinity_left.
  reflexivity.
Qed.

Lemma sm2_verifier_point_as_generator :
  forall private_key s t,
    0 <= private_key ->
    0 <= s ->
    0 <= t ->
    sm2_point_add
      (sm2_point_mul s SM2_G_POINT)
      (sm2_point_mul t
        (sm2_point_mul private_key SM2_G_POINT)) =
    sm2_point_mul
      ((s + t * private_key) mod SM2_N_Z) SM2_G_POINT.
Proof.
  intros private_key s t Hprivate Hs Ht.
  rewrite <- (sm2_point_mul_mul SM2_G_POINT private_key t)
    by assumption.
  replace (private_key * t) with (t * private_key) by ring.
  rewrite <- sm2_point_mul_add by lia.
  symmetry.
  apply sm2_generator_mul_mod.
  nia.
Qed.

Lemma sm2_generated_signature_algebra :
  forall private_key nonce r s inverse,
    valid_sm2_private_key private_key ->
    1 <= nonce < SM2_N_Z ->
    0 <= inverse < SM2_N_Z ->
    ((1 + private_key) * inverse) mod SM2_N_Z = 1 ->
    1 <= r < SM2_N_Z ->
    (r + nonce) mod SM2_N_Z <> 0 ->
    s = ((nonce - r * private_key) * inverse) mod SM2_N_Z ->
    1 <= s < SM2_N_Z ->
    let t := (r + s) mod SM2_N_Z in
    t <> 0 /\
    (s + t * private_key) mod SM2_N_Z = nonce.
Proof.
  intros private_key nonce r s inverse Hprivate Hnonce
    Hinverse_range Hinverse Hr Hrnonce Hs Hs_range.
  set (t := (r + s) mod SM2_N_Z).
  pose proof sm2_n_bounds as Hn.
  pose proof
    (Z.div_mod ((1 + private_key) * inverse)
      SM2_N_Z ltac:(lia)) as Einverse.
  rewrite Hinverse in Einverse.
  pose proof
    (Z.div_mod ((nonce - r * private_key) * inverse)
      SM2_N_Z ltac:(lia)) as Es.
  rewrite <- Hs in Es.
  pose proof (Z.div_mod (r + s) SM2_N_Z ltac:(lia)) as Et.
  fold t in Et.
  set (factor := 1 + private_key).
  set (difference := nonce - r * private_key).
  set (inverse_quotient :=
    ((1 + private_key) * inverse) / SM2_N_Z).
  set (s_quotient :=
    ((nonce - r * private_key) * inverse) / SM2_N_Z).
  set (t_quotient := (r + s) / SM2_N_Z).
  change
    (factor * inverse =
      SM2_N_Z * inverse_quotient + 1) in Einverse.
  change
    (difference * inverse =
      SM2_N_Z * s_quotient + s) in Es.
  change (r + s = SM2_N_Z * t_quotient + t) in Et.
  assert (Hs_factor :
    s * factor =
      difference +
      SM2_N_Z *
        (difference * inverse_quotient - s_quotient * factor)).
  {
    replace s with
      (difference * inverse - SM2_N_Z * s_quotient) by nia.
    replace
      ((difference * inverse - SM2_N_Z * s_quotient) * factor)
      with
      (difference * (factor * inverse) -
       SM2_N_Z * s_quotient * factor) by ring.
    rewrite Einverse.
    ring.
  }
  split.
  - intros Ht_zero.
    assert (Hsum_factor :
      (r + s) * factor = SM2_N_Z * t_quotient * factor).
    {
      rewrite Et, Ht_zero.
      ring.
    }
    set (quotient :=
      t_quotient * factor - difference * inverse_quotient +
      s_quotient * factor).
    assert (Hr_nonce : r + nonce = SM2_N_Z * quotient).
    {
      transitivity (r * factor + difference).
      { unfold factor, difference. ring. }
      transitivity
        (r * factor + s * factor -
         SM2_N_Z *
           (difference * inverse_quotient - s_quotient * factor)).
      { rewrite Hs_factor. ring. }
      transitivity
        ((r + s) * factor -
         SM2_N_Z *
           (difference * inverse_quotient - s_quotient * factor)).
      { ring. }
      rewrite Hsum_factor.
      unfold quotient.
      ring.
    }
    apply Hrnonce.
    apply (proj2 (Z.mod_divide (r + nonce) SM2_N_Z ltac:(lia))).
    exists quotient.
    rewrite Hr_nonce.
    ring.
  - apply sm2_n_mod_eq_of_divide; [lia |].
    set (quotient :=
      difference * inverse_quotient - s_quotient * factor -
      t_quotient * private_key).
    assert (Hscalar :
      s + t * private_key = nonce + SM2_N_Z * quotient).
    {
      replace t with (r + s - SM2_N_Z * t_quotient) by nia.
      transitivity
        (s * factor + r * private_key -
         SM2_N_Z * t_quotient * private_key).
      { unfold factor. ring. }
      rewrite Hs_factor.
      unfold difference, quotient.
      unfold difference.
      ring.
    }
    exists quotient.
    rewrite Hscalar.
    ring.
Qed.

Lemma sm2_verifier_signature_algebra :
  forall private_key r s t inverse nonce,
    valid_sm2_private_key private_key ->
    1 <= r < SM2_N_Z ->
    1 <= s < SM2_N_Z ->
    t = (r + s) mod SM2_N_Z ->
    t <> 0 ->
    0 <= inverse < SM2_N_Z ->
    ((1 + private_key) * inverse) mod SM2_N_Z = 1 ->
    nonce = (s + t * private_key) mod SM2_N_Z ->
    nonce <> 0 ->
    (r + nonce) mod SM2_N_Z <> 0 /\
    ((nonce - r * private_key) * inverse) mod SM2_N_Z = s.
Proof.
  intros private_key r s t inverse nonce Hprivate Hr Hs
    Ht Ht_nonzero Hinverse_range Hinverse Hnonce Hnonce_nonzero.
  pose proof sm2_n_bounds as Hn.
  assert (Ht_range : 0 <= t < SM2_N_Z).
  { rewrite Ht. apply Z.mod_pos_bound. lia. }
  assert (Hnonce_range : 0 <= nonce < SM2_N_Z).
  { rewrite Hnonce. apply Z.mod_pos_bound. lia. }
  pose proof
    (Z.div_mod ((1 + private_key) * inverse)
      SM2_N_Z ltac:(lia)) as Einverse.
  rewrite Hinverse in Einverse.
  pose proof (Z.div_mod (r + s) SM2_N_Z ltac:(lia)) as Et.
  rewrite <- Ht in Et.
  pose proof
    (Z.div_mod (s + t * private_key) SM2_N_Z ltac:(lia)) as Enonce.
  rewrite <- Hnonce in Enonce.
  split.
  - intros Hrnonce_zero.
    apply (proj1
      (Z.mod_divide (r + nonce) SM2_N_Z ltac:(lia)))
      in Hrnonce_zero.
    destruct Hrnonce_zero as [quotient Hquotient].
    apply Ht_nonzero.
    assert (Hdivide : (SM2_N_Z | t - 0)).
    {
      exists
        ((quotient - (r + s) / SM2_N_Z +
          (s + t * private_key) / SM2_N_Z) * inverse -
         t * (((1 + private_key) * inverse) / SM2_N_Z)).
      nia.
    }
    pose proof (sm2_n_mod_eq_of_divide t 0 ltac:(lia) Hdivide)
      as Ht_mod.
    rewrite Z.mod_small in Ht_mod by exact Ht_range.
    exact Ht_mod.
  - apply sm2_n_mod_eq_of_divide; [lia |].
    exists
      (s * (((1 + private_key) * inverse) / SM2_N_Z) -
       (((s + t * private_key) / SM2_N_Z) +
        private_key * ((r + s) / SM2_N_Z)) * inverse).
    nia.
Qed.

Lemma valid_sm2_keypair_public_noninfinity :
  forall private_key public_key,
    valid_sm2_keypair private_key public_key ->
    public_key <> ECInfinity.
Proof.
  intros private_key public_key [Hprivate ->].
  apply sm2_generator_exact_order.
  apply valid_sm2_private_key_bounds.
  exact Hprivate.
Qed.

Lemma valid_sm2_public_key_noninfinity :
  forall public_key,
    valid_sm2_public_key public_key ->
    public_key <> ECInfinity.
Proof.
  intros public_key [private_key Hkeypair].
  exact
    (valid_sm2_keypair_public_noninfinity
      private_key public_key Hkeypair).
Qed.

Lemma sm2_point_coordinates_represent :
  forall point,
    afpoint_represents (sm2_point_x point) (sm2_point_y point) point.
Proof.
  intros point.
  destruct point as [|point_x point_y Hcurve].
  - cbn [sm2_point_x sm2_point_y afpoint_represents afpoint_infinity].
    split; reflexivity.
  - cbn [sm2_point_x sm2_point_y afpoint_represents].
    split; reflexivity.
Qed.

Lemma afpoint_represents_sm2_point_coordinates :
  forall x y point,
    afpoint_represents x y point ->
    x = sm2_point_x point /\ y = sm2_point_y point.
Proof.
  intros x y point Hrepresents.
  destruct point as [|point_x point_y Hcurve].
  - cbn [afpoint_represents afpoint_infinity
         sm2_point_x sm2_point_y] in Hrepresents.
    exact Hrepresents.
  - cbn [afpoint_represents sm2_point_x sm2_point_y] in Hrepresents.
    exact Hrepresents.
Qed.

Lemma valid_sm2_public_key_coordinates :
  forall public_key,
    valid_sm2_public_key public_key ->
    afpoint_represents
      (sm2_point_x public_key) (sm2_point_y public_key) public_key.
Proof.
  intros public_key _.
  apply sm2_point_coordinates_represent.
Qed.

Lemma valid_sm2_public_key_coordinate_bounds :
  forall public_key,
    valid_sm2_public_key public_key ->
    0 <= sm2_point_x public_key < SM2_P_Z /\
    0 <= sm2_point_y public_key < SM2_P_Z.
Proof.
  intros public_key Hvalid.
  apply
    (afpoint_represents_bounds
      (sm2_point_x public_key) (sm2_point_y public_key) public_key).
  apply valid_sm2_public_key_coordinates.
  exact Hvalid.
Qed.

Lemma sm2_za_digest_length :
  forall id public_key,
    Zlength (sm2_za_digest id public_key) = 32.
Proof.
  intros id public_key.
  apply sm3_digest_bytes_length.
Qed.

Lemma sm2_za_digest_bounded :
  forall id public_key,
    u8_list_bounded (sm2_za_digest id public_key).
Proof.
  intros id public_key.
  apply sm3_digest_bytes_bounded.
Qed.

Lemma sm2_message_digest_length :
  forall id public_key message,
    Zlength (sm2_message_digest id public_key message) = 32.
Proof.
  intros id public_key message.
  apply sm3_digest_bytes_length.
Qed.

Lemma sm2_message_digest_bounded :
  forall id public_key message,
    u8_list_bounded (sm2_message_digest id public_key message).
Proof.
  intros id public_key message.
  apply sm3_digest_bytes_bounded.
Qed.

Lemma sm2_signature_verifies_generated_iff :
  forall digest public_key r s,
    valid_sm2_public_key public_key ->
    (sm2_signature_verifies digest public_key r s <->
     exists private_key,
       valid_sm2_keypair private_key public_key /\
       sm2_signature_generated digest private_key r s).
Proof.
  intros digest public_key r s Hpublic.
  split.
  - intros Hverifier.
    destruct Hpublic as [private_key Hkeypair].
    destruct Hkeypair as [Hprivate Hpublic_key].
    subst public_key.
    unfold sm2_signature_verifies in Hverifier.
    cbn zeta in Hverifier.
    destruct Hverifier as
      [Hr [Hs [Ht [Hresult [x [y [Hcoordinates Hr_equation]]]]]]].
    set (t := (r + s) mod SM2_N_Z) in *.
    set (nonce := (s + t * private_key) mod SM2_N_Z).
    assert (Ht_range : 0 <= t < SM2_N_Z).
    {
      unfold t.
      apply Z.mod_pos_bound.
      pose proof sm2_n_bounds. lia.
    }
    assert (Hnonce_range : 0 <= nonce < SM2_N_Z).
    {
      unfold nonce.
      apply Z.mod_pos_bound.
      pose proof sm2_n_bounds. lia.
    }
    assert (Hpoint :
      sm2_point_add
        (sm2_point_mul s SM2_G_POINT)
        (sm2_point_mul t
          (sm2_point_mul private_key SM2_G_POINT)) =
      sm2_point_mul nonce SM2_G_POINT).
    {
      unfold nonce.
      apply sm2_verifier_point_as_generator.
      - pose proof
          (valid_sm2_private_key_bounds private_key Hprivate).
        lia.
      - lia.
      - lia.
    }
    assert (Hnonce_nonzero : nonce <> 0).
    {
      intros Hnonce_zero.
      apply Hresult.
      rewrite Hpoint, Hnonce_zero, sm2_point_mul_zero.
      reflexivity.
    }
    destruct (sm2_n_mod_inverse_exists (1 + private_key))
      as [inverse [Hinverse_range Hinverse]].
    {
      unfold valid_sm2_private_key in Hprivate.
      lia.
    }
    pose proof
      (sm2_verifier_signature_algebra
        private_key r s t inverse nonce
        Hprivate Hr Hs eq_refl Ht
        Hinverse_range Hinverse eq_refl Hnonce_nonzero)
      as [Hr_nonce Hs_equation].
    exists private_key.
    split.
    + split; [exact Hprivate | reflexivity].
    + unfold sm2_signature_generated.
      split; [exact Hprivate |].
      exists nonce, x, y, inverse.
      split; [lia |].
      split.
      * rewrite <- Hpoint. exact Hcoordinates.
      * split; [exact Hinverse_range |].
        split; [exact Hinverse |].
        split; [exact Hr_equation |].
        split; [exact Hr |].
        split; [exact Hr_nonce |].
        split; [symmetry; exact Hs_equation | exact Hs].
  - intros Hgenerated_witness.
    destruct Hgenerated_witness as
      [private_key [Hkeypair Hgenerated]].
    destruct Hkeypair as [Hprivate Hpublic_key].
    subst public_key.
    unfold sm2_signature_generated in Hgenerated.
    destruct Hgenerated as [Hprivate_generated Hgenerated].
    destruct Hgenerated as [nonce [x [y [inverse Hgenerated]]]].
    destruct Hgenerated as
      [Hnonce
       [Hcoordinates
        [Hinverse_range
         [Hinverse
          [Hr_equation
           [Hr [Hr_nonce [Hs_equation Hs]]]]]]]].
    set (t := (r + s) mod SM2_N_Z).
    assert (Ht_range : 0 <= t < SM2_N_Z).
    {
      unfold t.
      apply Z.mod_pos_bound.
      pose proof sm2_n_bounds. lia.
    }
    pose proof
      (sm2_generated_signature_algebra
        private_key nonce r s inverse
        Hprivate_generated Hnonce Hinverse_range Hinverse
        Hr Hr_nonce Hs_equation Hs)
      as [Ht Hscalar].
    fold t in Ht, Hscalar.
    assert (Hpoint :
      sm2_point_add
        (sm2_point_mul s SM2_G_POINT)
        (sm2_point_mul t
          (sm2_point_mul private_key SM2_G_POINT)) =
      sm2_point_mul nonce SM2_G_POINT).
    {
      rewrite <- Hscalar.
      apply sm2_verifier_point_as_generator.
      - pose proof (valid_sm2_private_key_bounds
          private_key Hprivate_generated).
        lia.
      - lia.
      - lia.
    }
    unfold sm2_signature_verifies.
    split; [exact Hr |].
    split; [exact Hs |].
    cbn zeta.
    fold t.
    split; [exact Ht |].
    split.
    + rewrite Hpoint.
      apply sm2_generator_exact_order.
      lia.
    + exists x, y.
      split.
      * rewrite Hpoint. exact Hcoordinates.
      * exact Hr_equation.
Qed.

Lemma sm2_generated_signature_verifies :
  forall digest private_key public_key r s,
    valid_sm2_keypair private_key public_key ->
    sm2_signature_generated digest private_key r s ->
    sm2_signature_verifies digest public_key r s.
Proof.
  intros digest private_key public_key r s Hkeypair Hgenerated.
  assert (Hpublic : valid_sm2_public_key public_key).
  { exists private_key. exact Hkeypair. }
  apply (proj2
    (sm2_signature_verifies_generated_iff
      digest public_key r s Hpublic)).
  exists private_key. split; assumption.
Qed.

Lemma store_sm2_private_key_unfold :
  forall address private_key,
    store_sm2_private_key address private_key --||--
    “ valid_sm2_private_key private_key ” &&
    store_fn (&(address # "PrivKey" ->ₛ "da")) private_key.
Proof. intros. reflexivity. Qed.
