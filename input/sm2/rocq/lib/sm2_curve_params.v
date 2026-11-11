(** Fixed parameters of the standard SM2 curve. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.EE.Applications_human.sm2.lib Require Export sm2_common_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition SM2_A_Z : Z := SM2_P_Z - 3.

Definition SM2_B_LIMB_0 : Z := 15977853666175749779.
Definition SM2_B_LIMB_1 : Z := 17552649758423355282.
Definition SM2_B_LIMB_2 : Z := 5573941537263651239.
Definition SM2_B_LIMB_3 : Z := 2948162990246944308.

Definition SM2_B_Z : Z :=
  u256_of_limbs
    SM2_B_LIMB_0 SM2_B_LIMB_1 SM2_B_LIMB_2 SM2_B_LIMB_3.

(** Canonical residue of [1 / 2] in the SM2 base field. *)
Definition SM2_P_INV2_Z : Z :=
  57896044605178124378210172607010446383125176995962095727210596966644842496000.

Definition SM2_G_X_LIMB_0 : Z := 0x715A4589334C74C7.
Definition SM2_G_X_LIMB_1 : Z := 0x8FE30BBFF2660BE1.
Definition SM2_G_X_LIMB_2 : Z := 0x5F9904466A39C994.
Definition SM2_G_X_LIMB_3 : Z := 0x32C4AE2C1F198119.

Definition SM2_G_Y_LIMB_0 : Z := 0x02DF32E52139F0A0.
Definition SM2_G_Y_LIMB_1 : Z := 0xD0A9877CC62A4740.
Definition SM2_G_Y_LIMB_2 : Z := 0x59BDCEE36B692153.
Definition SM2_G_Y_LIMB_3 : Z := 0xBC3736A2F4F6779C.

Definition SM2_G_X_LIMBS : list Z :=
  [SM2_G_X_LIMB_0; SM2_G_X_LIMB_1;
   SM2_G_X_LIMB_2; SM2_G_X_LIMB_3].

Definition SM2_G_Y_LIMBS : list Z :=
  [SM2_G_Y_LIMB_0; SM2_G_Y_LIMB_1;
   SM2_G_Y_LIMB_2; SM2_G_Y_LIMB_3].

Definition SM2_G_X_Z : Z :=
  u256_of_limbs
    SM2_G_X_LIMB_0 SM2_G_X_LIMB_1
    SM2_G_X_LIMB_2 SM2_G_X_LIMB_3.

Definition SM2_G_Y_Z : Z :=
  u256_of_limbs
    SM2_G_Y_LIMB_0 SM2_G_Y_LIMB_1
    SM2_G_Y_LIMB_2 SM2_G_Y_LIMB_3.

Lemma sm2_a_bounds :
  0 <= SM2_A_Z < SM2_P_Z.
Proof.
  cbv [SM2_A_Z SM2_P_Z].
  lia.
Qed.

Lemma sm2_b_bounds :
  0 <= SM2_B_Z < SM2_P_Z.
Proof.
  vm_compute.
  split; congruence.
Qed.

Lemma sm2_g_x_bounds :
  0 <= SM2_G_X_Z < SM2_P_Z.
Proof.
  vm_compute.
  split; congruence.
Qed.

Lemma sm2_g_y_bounds :
  0 <= SM2_G_Y_Z < SM2_P_Z.
Proof.
  vm_compute.
  split; congruence.
Qed.

Lemma sm2_p_inv2_twice :
  2 * SM2_P_INV2_Z = SM2_P_Z + 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sm2_p_gt_one :
  1 < SM2_P_Z.
Proof.
  pose proof sm2_p_montgomery_bounds.
  lia.
Qed.
