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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition ecc_representation_strategy10 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (ry : Z) (rx : Z),
      TT &&
      (“ (x = rx) ”) &&
      (“ (y = ry) ”) &&
      emp -*
      TT &&
      emp **
      ((store_afpoint_fields p rx ry))
      ).

Definition ecc_representation_strategy13 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 &( ((p)) # "AFPoint" ->ₛ "y") y))
    ) ** (
    ALL (rx : Z),
      TT &&
      (“ (x = rx) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((p)) # "AFPoint" ->ₛ "x") rx))
      ).

Definition ecc_representation_strategy14 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 &( ((p)) # "AFPoint" ->ₛ "x") x))
    ) ** (
    ALL (ry : Z),
      TT &&
      (“ (y = ry) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((p)) # "AFPoint" ->ₛ "y") ry))
      ).

Definition ecc_representation_strategy110 :=
  forall (p : Z) (q : Z) (x : Z) (y : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp &( ((p)) # "AFPoint" ->ₛ "y") y))
    ) ** (
    ALL (rx : Z),
      TT &&
      (“ (x = rx) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fp &( ((q)) # "AFPoint" ->ₛ "x") rx))
      ).

Definition ecc_representation_strategy111 :=
  forall (p : Z) (q : Z) (x : Z) (y : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    emp **
    ((store_fp &( ((p)) # "AFPoint" ->ₛ "x") x))
    ) ** (
    ALL (ry : Z),
      TT &&
      (“ (y = ry) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fp &( ((q)) # "AFPoint" ->ₛ "y") ry))
      ).

Definition ecc_representation_strategy20 :=
  forall (p : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (rz : Z) (rx : Z) (ry : Z),
      TT &&
      (“ (x = rx) ”) &&
      (“ (y = ry) ”) &&
      (“ (z = rz) ”) &&
      emp -*
      TT &&
      emp **
      ((store_jpoint_fields p rx ry rz))
      ).

Definition ecc_representation_strategy120 :=
  forall (p : Z) (q : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "y") y)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    ALL (rx : Z),
      TT &&
      (“ (x = rx) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fp &( ((q)) # "JPoint" ->ₛ "x") rx))
      ).

Definition ecc_representation_strategy121 :=
  forall (p : Z) (q : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    ALL (ry : Z),
      TT &&
      (“ (y = ry) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fp &( ((q)) # "JPoint" ->ₛ "y") ry))
      ).

Definition ecc_representation_strategy122 :=
  forall (p : Z) (q : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "y") y))
    ) ** (
    ALL (rz : Z),
      TT &&
      (“ (z = rz) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fp &( ((q)) # "JPoint" ->ₛ "z") rz))
      ).

Definition ecc_representation_strategy126 :=
  forall (p : Z) (q : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "y") y)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((q)) # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4))
    ).

Definition ecc_representation_strategy127 :=
  forall (p : Z) (q : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((q)) # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4))
    ).

Definition ecc_representation_strategy128 :=
  forall (p : Z) (q : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "y") y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((q)) # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v") 4))
    ).

Definition ecc_representation_strategy130 :=
  forall (p : Z) (q : Z) (x : Z) (y : Z) (z : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 z) ”) &&
    (“ (Z.lt z ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 &( ((p)) # "JPoint" ->ₛ "y") y)) **
    ((store_u256 &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    ALL (rx : Z),
      TT &&
      (“ (x = rx) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((q)) # "JPoint" ->ₛ "x") rx))
      ).

Definition ecc_representation_strategy131 :=
  forall (p : Z) (q : Z) (x : Z) (y : Z) (z : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 z) ”) &&
    (“ (Z.lt z ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_u256 &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    ALL (ry : Z),
      TT &&
      (“ (y = ry) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((q)) # "JPoint" ->ₛ "y") ry))
      ).

Definition ecc_representation_strategy132 :=
  forall (p : Z) (q : Z) (x : Z) (y : Z) (z : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 z) ”) &&
    (“ (Z.lt z ( SM2_P_Z)) ”) &&
    emp **
    ((store_u256 &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_u256 &( ((p)) # "JPoint" ->ₛ "y") y))
    ) ** (
    ALL (rz : Z),
      TT &&
      (“ (z = rz) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((q)) # "JPoint" ->ₛ "z") rz))
      ).

Definition ecc_representation_strategy30 :=
  forall (p : Z) (point : ec_point),
    TT &&
    emp **
    ((store_afpoint p point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_afpoint p point))
    ).

Definition ecc_representation_strategy40 :=
  forall (p : Z) (point : ec_point),
    TT &&
    emp **
    ((store_jpoint p point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_jpoint p point))
    ).

Definition ecc_representation_strategy50 :=
  forall (p : Z) (point : ec_point),
    TT &&
    emp **
    ((store_jpoint_with_canonical_infinity p point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_jpoint_with_canonical_infinity p point))
    ).

Definition ecc_representation_strategy60 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_mont_afpoint_coords p x y))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (ry : Z) (rx : Z),
      TT &&
      (“ (x = rx) ”) &&
      (“ (y = ry) ”) &&
      emp -*
      TT &&
      emp **
      ((store_mont_afpoint_coords p rx ry))
      ).

Definition ecc_representation_strategy70 :=
  forall (p : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_mont_jpoint_coords p x y z))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (rz : Z) (rx : Z) (ry : Z),
      TT &&
      (“ (x = rx) ”) &&
      (“ (y = ry) ”) &&
      (“ (z = rz) ”) &&
      emp -*
      TT &&
      emp **
      ((store_mont_jpoint_coords p rx ry rz))
      ).

Definition ecc_representation_strategy80 :=
  forall (p : Z) (point : ec_point),
    TT &&
    emp **
    ((store_mont_afpoint p point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_afpoint p point))
    ).

Definition ecc_representation_strategy90 :=
  forall (p : Z) (point : ec_point),
    TT &&
    emp **
    ((store_mont_jpoint p point))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_mont_jpoint p point))
    ).

Definition ecc_representation_strategy11 :=
  forall (p : Z) (y : Z) (x : Z),
    TT &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "AFPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "AFPoint" ->ₛ "y") y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_representation_strategy112 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_afpoint_fields p x y))
    |--
    EX (xs : (@list Z)) (ys : (@list Z)),
      (
      TT &&
      (“ (Z.le 0 x) ”) &&
      (“ (Z.lt x ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z xs) = 4) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = x) ”) &&
      (“ (Z.le 0 y) ”) &&
      (“ (Z.lt y ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z ys) = 4) ”) &&
      (“ (u64_list_bounded ys) ”) &&
      (“ (( u64_list_value ys) = y) ”) &&
      emp **
      ((UInt64Array.full &( ((&( ((p)) # "AFPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4 xs)) **
      ((UInt64Array.full &( ((&( ((p)) # "AFPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4 ys))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy21 :=
  forall (p : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "y") y)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "z") z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_representation_strategy129 :=
  forall (z : Z) (x : Z) (y : Z) (p : Z),
    TT &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    EX (xs : (@list Z)) (ys : (@list Z)) (zs : (@list Z)),
      (
      TT &&
      (“ (Z.le 0 x) ”) &&
      (“ (Z.lt x ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z xs) = 4) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = x) ”) &&
      (“ (Z.le 0 y) ”) &&
      (“ (Z.lt y ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z ys) = 4) ”) &&
      (“ (u64_list_bounded ys) ”) &&
      (“ (( u64_list_value ys) = y) ”) &&
      (“ (Z.le 0 z) ”) &&
      (“ (Z.lt z ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z zs) = 4) ”) &&
      (“ (u64_list_bounded zs) ”) &&
      (“ (( u64_list_value zs) = z) ”) &&
      emp **
      ((UInt64Array.full &( ((&( ((p)) # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4 xs)) **
      ((UInt64Array.full &( ((&( ((p)) # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4 ys)) **
      ((UInt64Array.full &( ((&( ((p)) # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v") 4 zs))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy31 :=
  forall (point : ec_point) (p : Z),
    TT &&
    emp **
    ((store_afpoint p point))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      (“ (afpoint_represents x y point) ”) &&
      emp **
      ((store_afpoint_fields p x y))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy41 :=
  forall (point : ec_point) (p : Z),
    TT &&
    emp **
    ((store_jpoint p point))
    |--
    EX (x : Z) (y : Z) (z : Z),
      (
      TT &&
      (“ (jpoint_represents x y z point) ”) &&
      emp **
      ((store_jpoint_fields p x y z))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy51 :=
  forall (point : ec_point) (p : Z),
    TT &&
    emp **
    ((store_jpoint_with_canonical_infinity p point))
    |--
    EX (x : Z) (y : Z) (z : Z),
      (
      TT &&
      (“ (jpoint_represents x y z point) ”) &&
      (“ (jpoint_canonical_infinity_encoding x y z point) ”) &&
      emp **
      ((store_jpoint_fields p x y z))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy61 :=
  forall (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_mont_afpoint_coords p x y))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    emp **
    ((store_afpoint_fields p ( mont_p x) ( mont_p y)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_representation_strategy71 :=
  forall (z : Z) (y : Z) (x : Z) (p : Z),
    TT &&
    emp **
    ((store_mont_jpoint_coords p x y z))
    |--
    (
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 z) ”) &&
    (“ (Z.lt z ( SM2_P_Z)) ”) &&
    emp **
    ((store_jpoint_fields p ( mont_p x) ( mont_p y) ( mont_p z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_representation_strategy81 :=
  forall (point : ec_point) (p : Z),
    TT &&
    emp **
    ((store_mont_afpoint p point))
    |--
    EX (x : Z) (y : Z),
      (
      TT &&
      (“ (afpoint_represents x y point) ”) &&
      emp **
      ((store_mont_afpoint_coords p x y))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy91 :=
  forall (point : ec_point) (p : Z),
    TT &&
    emp **
    ((store_mont_jpoint p point))
    |--
    EX (x : Z) (y : Z) (z : Z),
      (
      TT &&
      (“ (jpoint_represents x y z point) ”) &&
      emp **
      ((store_mont_jpoint_coords p x y z))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition ecc_representation_strategy18 :=
  forall (p : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    emp **
    ((store_jpoint_fields p x y z))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v") 4))
    ).

Definition ecc_representation_strategy12 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (x : Z) (p : Z) (y : Z),
    TT &&
    emp **
    ((store_fp &( ((p)) # "AFPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "AFPoint" ->ₛ "y") y)) -*
    TT &&
    emp **
    ((store_afpoint_fields p x y))
    ).

Definition ecc_representation_strategy22 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (x : Z) (p : Z) (z : Z),
    TT &&
    emp **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "y") y)) **
    ((store_fp &( ((p)) # "JPoint" ->ₛ "z") z)) -*
    TT &&
    emp **
    ((store_jpoint_fields p x y z))
    ).

Definition ecc_representation_strategy32 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (point : ec_point) (x : Z) (p : Z),
    TT &&
    (“ (afpoint_represents x y point) ”) &&
    emp **
    ((store_afpoint_fields p x y)) -*
    TT &&
    emp **
    ((store_afpoint p point))
    ).

Definition ecc_representation_strategy42 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (point : ec_point) (z : Z) (x : Z) (p : Z),
    TT &&
    (“ (jpoint_represents x y z point) ”) &&
    emp **
    ((store_jpoint_fields p x y z)) -*
    TT &&
    emp **
    ((store_jpoint p point))
    ).

Definition ecc_representation_strategy52 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (point : ec_point) (z : Z) (x : Z) (p : Z),
    TT &&
    (“ (jpoint_represents x y z point) ”) &&
    (“ (jpoint_canonical_infinity_encoding x y z point) ”) &&
    emp **
    ((store_jpoint_fields p x y z)) -*
    TT &&
    emp **
    ((store_jpoint_with_canonical_infinity p point))
    ).

Definition ecc_representation_strategy62 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    emp **
    ((store_afpoint_fields p ( mont_p x) ( mont_p y))) -*
    TT &&
    emp **
    ((store_mont_afpoint_coords p x y))
    ).

Definition ecc_representation_strategy72 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (z : Z) (y : Z) (x : Z) (p : Z),
    TT &&
    (“ (Z.le 0 x) ”) &&
    (“ (Z.lt x ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 y) ”) &&
    (“ (Z.lt y ( SM2_P_Z)) ”) &&
    (“ (Z.le 0 z) ”) &&
    (“ (Z.lt z ( SM2_P_Z)) ”) &&
    emp **
    ((store_jpoint_fields p ( mont_p x) ( mont_p y) ( mont_p z))) -*
    TT &&
    emp **
    ((store_mont_jpoint_coords p x y z))
    ).

Definition ecc_representation_strategy82 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (point : ec_point) (x : Z) (p : Z),
    TT &&
    (“ (afpoint_represents x y point) ”) &&
    emp **
    ((store_mont_afpoint_coords p x y)) -*
    TT &&
    emp **
    ((store_mont_afpoint p point))
    ).

Definition ecc_representation_strategy92 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (y : Z) (point : ec_point) (z : Z) (x : Z) (p : Z),
    TT &&
    (“ (jpoint_represents x y z point) ”) &&
    emp **
    ((store_mont_jpoint_coords p x y z)) -*
    TT &&
    emp **
    ((store_mont_jpoint p point))
    ).

Module Type ecc_representation_Strategy_Correct.

  Axiom ecc_representation_strategy10_correctness : ecc_representation_strategy10.
  Axiom ecc_representation_strategy13_correctness : ecc_representation_strategy13.
  Axiom ecc_representation_strategy14_correctness : ecc_representation_strategy14.
  Axiom ecc_representation_strategy110_correctness : ecc_representation_strategy110.
  Axiom ecc_representation_strategy111_correctness : ecc_representation_strategy111.
  Axiom ecc_representation_strategy20_correctness : ecc_representation_strategy20.
  Axiom ecc_representation_strategy120_correctness : ecc_representation_strategy120.
  Axiom ecc_representation_strategy121_correctness : ecc_representation_strategy121.
  Axiom ecc_representation_strategy122_correctness : ecc_representation_strategy122.
  Axiom ecc_representation_strategy126_correctness : ecc_representation_strategy126.
  Axiom ecc_representation_strategy127_correctness : ecc_representation_strategy127.
  Axiom ecc_representation_strategy128_correctness : ecc_representation_strategy128.
  Axiom ecc_representation_strategy130_correctness : ecc_representation_strategy130.
  Axiom ecc_representation_strategy131_correctness : ecc_representation_strategy131.
  Axiom ecc_representation_strategy132_correctness : ecc_representation_strategy132.
  Axiom ecc_representation_strategy30_correctness : ecc_representation_strategy30.
  Axiom ecc_representation_strategy40_correctness : ecc_representation_strategy40.
  Axiom ecc_representation_strategy50_correctness : ecc_representation_strategy50.
  Axiom ecc_representation_strategy60_correctness : ecc_representation_strategy60.
  Axiom ecc_representation_strategy70_correctness : ecc_representation_strategy70.
  Axiom ecc_representation_strategy80_correctness : ecc_representation_strategy80.
  Axiom ecc_representation_strategy90_correctness : ecc_representation_strategy90.
  Axiom ecc_representation_strategy11_correctness : ecc_representation_strategy11.
  Axiom ecc_representation_strategy112_correctness : ecc_representation_strategy112.
  Axiom ecc_representation_strategy21_correctness : ecc_representation_strategy21.
  Axiom ecc_representation_strategy129_correctness : ecc_representation_strategy129.
  Axiom ecc_representation_strategy31_correctness : ecc_representation_strategy31.
  Axiom ecc_representation_strategy41_correctness : ecc_representation_strategy41.
  Axiom ecc_representation_strategy51_correctness : ecc_representation_strategy51.
  Axiom ecc_representation_strategy61_correctness : ecc_representation_strategy61.
  Axiom ecc_representation_strategy71_correctness : ecc_representation_strategy71.
  Axiom ecc_representation_strategy81_correctness : ecc_representation_strategy81.
  Axiom ecc_representation_strategy91_correctness : ecc_representation_strategy91.
  Axiom ecc_representation_strategy18_correctness : ecc_representation_strategy18.
  Axiom ecc_representation_strategy12_correctness : ecc_representation_strategy12.
  Axiom ecc_representation_strategy22_correctness : ecc_representation_strategy22.
  Axiom ecc_representation_strategy32_correctness : ecc_representation_strategy32.
  Axiom ecc_representation_strategy42_correctness : ecc_representation_strategy42.
  Axiom ecc_representation_strategy52_correctness : ecc_representation_strategy52.
  Axiom ecc_representation_strategy62_correctness : ecc_representation_strategy62.
  Axiom ecc_representation_strategy72_correctness : ecc_representation_strategy72.
  Axiom ecc_representation_strategy82_correctness : ecc_representation_strategy82.
  Axiom ecc_representation_strategy92_correctness : ecc_representation_strategy92.

End ecc_representation_Strategy_Correct.
