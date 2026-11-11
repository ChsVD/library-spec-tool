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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_and_apoint_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition montg_add_jpoint_and_apoint_compare_strategy1 :=
  forall (y1 : Z) (z1 : Z) (y2 : Z) (x1 : Z) (x2 : Z) (h : Z) (r : Z),
    TT &&
    emp **
    ((store_fp h ( Zmod (Z.sub ( mont_p ( maja_u2 x2 z1)) ( mont_p x1)) ( SM2_P_Z)))) **
    ((store_fp r ( Zmod (Z.sub ( mont_p ( maja_s2 y2 z1)) ( mont_p y1)) ( SM2_P_Z))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( mont_p ( maja_h x1 x2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( maja_h x1 x2 z1)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( maja_r y1 y2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( maja_r y1 y2 z1)) ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256_limbs (Z.add &( ((h)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( maja_h x1 x2 z1)))) **
    ((store_u256_limbs (Z.add &( ((r)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( maja_r y1 y2 z1))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_compare_strategy2 :=
  forall (y1 : Z) (z1 : Z) (y2 : Z) (x1 : Z) (x2 : Z) (h : Z) (r : Z),
    TT &&
    (“ (Z.le 0 ( mont_p ( maja_h x1 x2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( maja_h x1 x2 z1)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( maja_r y1 y2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( maja_r y1 y2 z1)) ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256_limbs (Z.add &( ((h)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( maja_h x1 x2 z1)))) **
    ((store_u256_limbs (Z.add &( ((r)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( maja_r y1 y2 z1))))
    |--
    (
    TT &&
    emp **
    ((store_fp h ( mont_p ( maja_h x1 x2 z1)))) **
    ((store_fp r ( mont_p ( maja_r y1 y2 z1))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type montg_add_jpoint_and_apoint_compare_Strategy_Correct.

  Axiom montg_add_jpoint_and_apoint_compare_strategy1_correctness : montg_add_jpoint_and_apoint_compare_strategy1.
  Axiom montg_add_jpoint_and_apoint_compare_strategy2_correctness : montg_add_jpoint_and_apoint_compare_strategy2.

End montg_add_jpoint_and_apoint_compare_Strategy_Correct.
