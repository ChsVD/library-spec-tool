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
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition montg_add_jpoint_compare_strategy1 :=
  forall (y2 : Z) (z1 : Z) (y1 : Z) (z2 : Z) (x2 : Z) (x1 : Z) (s1 : Z) (u1 : Z) (u2 : Z) (s2 : Z),
    TT &&
    emp **
    ((store_fp u1 ( mont_p (Z.mul x1 ( aj_qz2 z2))))) **
    ((store_fp u2 ( mont_p (Z.mul x2 ( aj_pz2 z1))))) **
    ((store_fp s1 ( mont_p (Z.mul y1 ( aj_qz3 z2))))) **
    ((store_fp s2 ( mont_p (Z.mul y2 ( aj_pz3 z1)))))
    |--
    (
    TT &&
    (“ (Z.le 0 ( mont_p ( aj_u1 x1 z2))) ”) &&
    (“ (Z.lt ( mont_p ( aj_u1 x1 z2)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( aj_u2 x2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( aj_u2 x2 z1)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( aj_s1 y1 z2))) ”) &&
    (“ (Z.lt ( mont_p ( aj_s1 y1 z2)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( aj_s2 y2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( aj_s2 y2 z1)) ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256_limbs (Z.add &( ((u1)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_u1 x1 z2)))) **
    ((store_u256_limbs (Z.add &( ((u2)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_u2 x2 z1)))) **
    ((store_u256_limbs (Z.add &( ((s1)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_s1 y1 z2)))) **
    ((store_u256_limbs (Z.add &( ((s2)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_s2 y2 z1))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_compare_strategy2 :=
  forall (y2 : Z) (z1 : Z) (y1 : Z) (z2 : Z) (x2 : Z) (x1 : Z) (s1 : Z) (u1 : Z) (u2 : Z) (s2 : Z),
    TT &&
    (“ (Z.le 0 ( mont_p ( aj_u1 x1 z2))) ”) &&
    (“ (Z.lt ( mont_p ( aj_u1 x1 z2)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( aj_u2 x2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( aj_u2 x2 z1)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( aj_s1 y1 z2))) ”) &&
    (“ (Z.lt ( mont_p ( aj_s1 y1 z2)) ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 ( mont_p ( aj_s2 y2 z1))) ”) &&
    (“ (Z.lt ( mont_p ( aj_s2 y2 z1)) ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256_limbs (Z.add &( ((u1)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_u1 x1 z2)))) **
    ((store_u256_limbs (Z.add &( ((u2)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_u2 x2 z1)))) **
    ((store_u256_limbs (Z.add &( ((s1)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_s1 y1 z2)))) **
    ((store_u256_limbs (Z.add &( ((s2)) # "u32" ->ₛ "v") (Z.mul 0 (@sizeof_front_end_type FET_uint64))) ( mont_p ( aj_s2 y2 z1))))
    |--
    (
    TT &&
    emp **
    ((store_fp u1 ( mont_p ( aj_u1 x1 z2)))) **
    ((store_fp u2 ( mont_p ( aj_u2 x2 z1)))) **
    ((store_fp s1 ( mont_p ( aj_s1 y1 z2)))) **
    ((store_fp s2 ( mont_p ( aj_s2 y2 z1))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type montg_add_jpoint_compare_Strategy_Correct.

  Axiom montg_add_jpoint_compare_strategy1_correctness : montg_add_jpoint_compare_strategy1.
  Axiom montg_add_jpoint_compare_strategy2_correctness : montg_add_jpoint_compare_strategy2.

End montg_add_jpoint_compare_Strategy_Correct.
