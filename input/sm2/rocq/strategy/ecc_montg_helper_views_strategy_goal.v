Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition ecc_montg_helper_views_strategy10 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_u256_limbs (Z.add &( ((p)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x))
    |--
    (
    TT &&
    emp **
    ((store_u256 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_montg_helper_views_strategy11 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((store_u256_limbs p x))
    |--
    EX (x0 : Z) (x1 : Z) (x2 : Z) (x3 : Z),
      (
      TT &&
      (“ (Z.le 0 x0) ”) &&
      (“ (Z.lt x0 ( U64_MOD)) ”) &&
      (“ (Z.le 0 x1) ”) &&
      (“ (Z.lt x1 ( U64_MOD)) ”) &&
      (“ (Z.le 0 x2) ”) &&
      (“ (Z.lt x2 ( U64_MOD)) ”) &&
      (“ (Z.le 0 x3) ”) &&
      (“ (Z.lt x3 ( U64_MOD)) ”) &&
      (“ (x = ( u256_of_limbs x0 x1 x2 x3)) ”) &&
      emp **
      ((poly_store FET_uint64 (Z.add p (Z.mul 0 (@sizeof_front_end_type FET_uint64))) x0)) **
      ((poly_store FET_uint64 (Z.add p (Z.mul 1 (@sizeof_front_end_type FET_uint64))) x1)) **
      ((poly_store FET_uint64 (Z.add p (Z.mul 2 (@sizeof_front_end_type FET_uint64))) x2)) **
      ((poly_store FET_uint64 (Z.add p (Z.mul 3 (@sizeof_front_end_type FET_uint64))) x3))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_montg_helper_views_strategy20 :=
  forall (x : Z) (p : Z),
    TT &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256_limbs p x))
    |--
    (
    TT &&
    emp **
    ((store_fp p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_montg_helper_views_strategy21 :=
  forall (x : Z) (p : Z),
    TT &&
    (“ (Z.lt x ( SM2_N_Z)) ”) &&
    emp **
    ((store_u256_limbs p x))
    |--
    (
    TT &&
    emp **
    ((store_fn p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_montg_helper_views_strategy30 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_fp p x))
    |--
    (
    TT &&
    emp **
    ((store_u256_limbs p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_montg_helper_views_strategy31 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((store_fn p x))
    |--
    (
    TT &&
    emp **
    ((store_u256_limbs p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_montg_helper_views_strategy32 :=
  forall (slot : Z) (result : Z) (x : Z),
    TT &&
    emp **
    ((poly_store FET_ptr slot result)) **
    ((store_fp result x))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr slot result)) **
    ((store_u256_limbs result x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_montg_helper_views_strategy40 :=
  forall (p : Z),
    TT &&
    emp **
    ((UInt64Array.undef_full p 4))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 p))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type ecc_montg_helper_views_Strategy_Correct.

  Axiom ecc_montg_helper_views_strategy10_correctness : ecc_montg_helper_views_strategy10.
  Axiom ecc_montg_helper_views_strategy11_correctness : ecc_montg_helper_views_strategy11.
  Axiom ecc_montg_helper_views_strategy20_correctness : ecc_montg_helper_views_strategy20.
  Axiom ecc_montg_helper_views_strategy21_correctness : ecc_montg_helper_views_strategy21.
  Axiom ecc_montg_helper_views_strategy30_correctness : ecc_montg_helper_views_strategy30.
  Axiom ecc_montg_helper_views_strategy31_correctness : ecc_montg_helper_views_strategy31.
  Axiom ecc_montg_helper_views_strategy32_correctness : ecc_montg_helper_views_strategy32.
  Axiom ecc_montg_helper_views_strategy40_correctness : ecc_montg_helper_views_strategy40.

End ecc_montg_helper_views_Strategy_Correct.
