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

Definition wnaf3_precomp_points_strategy10 :=
  forall (positive : Z) (negative : Z),
    TT &&
    emp **
    ((wnaf3_precomp_undef positive negative))
    |--
    (
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( (((Z.add positive (Z.mul 1 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add positive (Z.mul 1 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add positive (Z.mul 3 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add positive (Z.mul 3 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add negative (Z.mul 1 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add negative (Z.mul 1 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add negative (Z.mul 3 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( (((Z.add negative (Z.mul 3 (@sizeof_front_end_type (FET_alias ("AFPoint"))))))) # "AFPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy11 :=
  forall (positive : Z) (negative : Z) (point : ec_point),
    TT &&
    emp **
    ((store_mont_afpoint (Z.add positive (Z.mul 1 (@sizeof_front_end_type (FET_alias ("AFPoint"))))) point)) **
    ((store_mont_afpoint (Z.add positive (Z.mul 3 (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_mul 3 point))) **
    ((store_mont_afpoint (Z.add negative (Z.mul 1 (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_negate point))) **
    ((store_mont_afpoint (Z.add negative (Z.mul 3 (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_negate ( sm2_point_mul 3 point))))
    |--
    (
    TT &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy20 :=
  forall (digit : Z) (positive : Z) (point : ec_point) (negative : Z),
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.gt digit 0) ”) &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    |--
    (
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.gt digit 0) ”) &&
    emp **
    ((store_mont_afpoint (Z.add positive (Z.mul digit (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_mul digit point))) **
    ((store_mont_wnaf3_precomp_rest positive negative point digit))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy21 :=
  forall (digit : Z) (positive : Z) (point : ec_point) (negative : Z),
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.gt digit 0) ”) &&
    emp **
    ((store_mont_afpoint (Z.add positive (Z.mul digit (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_mul digit point))) **
    ((store_mont_wnaf3_precomp_rest positive negative point digit))
    |--
    (
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.gt digit 0) ”) &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy22 :=
  forall (digit : Z) (positive : Z) (point : ec_point) (negative : Z),
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.lt digit 0) ”) &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    |--
    (
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.lt digit 0) ”) &&
    emp **
    ((store_mont_afpoint (Z.add negative (Z.mul (Z.opp digit) (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_negate ( sm2_point_mul (Z.opp digit) point)))) **
    ((store_mont_wnaf3_precomp_rest positive negative point digit))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy23 :=
  forall (digit : Z) (positive : Z) (point : ec_point) (negative : Z),
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.lt digit 0) ”) &&
    emp **
    ((store_mont_afpoint (Z.add negative (Z.mul (Z.opp digit) (@sizeof_front_end_type (FET_alias ("AFPoint"))))) ( sm2_point_negate ( sm2_point_mul (Z.opp digit) point)))) **
    ((store_mont_wnaf3_precomp_rest positive negative point digit))
    |--
    (
    TT &&
    (“ (wnaf3_digit digit) ”) &&
    (“ (Z.lt digit 0) ”) &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy30 :=
  forall (positive : Z),
    TT &&
    emp **
    ((StructAFPointArray.undef_full positive 4))
    |--
    (
    TT &&
    emp **
    ((wnaf3_positive_array_undef positive))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy31 :=
  forall (negative : Z),
    TT &&
    emp **
    ((StructAFPointArray.undef_full negative 4))
    |--
    (
    TT &&
    emp **
    ((wnaf3_negative_array_undef negative))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy32 :=
  forall (positive : Z) (negative : Z),
    TT &&
    emp **
    ((wnaf3_positive_array_undef positive)) **
    ((wnaf3_negative_array_undef negative))
    |--
    (
    TT &&
    emp **
    ((wnaf3_precomp_undef positive negative)) **
    ((wnaf3_precomp_unused positive negative))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy33 :=
  forall (point : ec_point) (positive : Z) (negative : Z),
    TT &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point)) **
    ((wnaf3_precomp_unused positive negative))
    |--
    (
    TT &&
    emp **
    ((StructAFPointArray.undef_full positive 4)) **
    ((StructAFPointArray.undef_full negative 4))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy35 :=
  forall (positive : Z) (point : ec_point) (negative : Z),
    TT &&
    emp **
    ((store_mont_wnaf3_precomp (Z.add positive (Z.mul 0 (@sizeof_front_end_type (FET_alias ("AFPoint"))))) (Z.add negative (Z.mul 0 (@sizeof_front_end_type (FET_alias ("AFPoint"))))) point))
    |--
    (
    TT &&
    emp **
    ((store_mont_wnaf3_precomp positive negative point))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy41 :=
  forall (scalar : Z) (address : Z),
    TT &&
    emp **
    ((store_wnaf3 address scalar))
    |--
    EX (digits : (@list Z)),
      (
      TT &&
      (“ (wnaf3_representation scalar digits) ”) &&
      emp **
      ((CharArray.full address 257 digits))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition wnaf3_precomp_points_strategy42 :=
  forall (address : Z) (digits : (@list Z)),
    TT &&
    emp **
    ((CharArray.full address 257 digits))
    |--
    (
    TT &&
    emp **
    ((CharArray.undef_full address 257))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition wnaf3_precomp_points_strategy43 :=
  forall (address : Z) (digits : (@list Z)),
    TT &&
    emp **
    ((CharArray.full (Z.add address (Z.mul 0 (@sizeof_front_end_type FET_char))) 257 digits))
    |--
    (
    TT &&
    emp **
    ((CharArray.full address 257 digits))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type wnaf3_precomp_points_Strategy_Correct.

  Axiom wnaf3_precomp_points_strategy10_correctness : wnaf3_precomp_points_strategy10.
  Axiom wnaf3_precomp_points_strategy11_correctness : wnaf3_precomp_points_strategy11.
  Axiom wnaf3_precomp_points_strategy20_correctness : wnaf3_precomp_points_strategy20.
  Axiom wnaf3_precomp_points_strategy21_correctness : wnaf3_precomp_points_strategy21.
  Axiom wnaf3_precomp_points_strategy22_correctness : wnaf3_precomp_points_strategy22.
  Axiom wnaf3_precomp_points_strategy23_correctness : wnaf3_precomp_points_strategy23.
  Axiom wnaf3_precomp_points_strategy30_correctness : wnaf3_precomp_points_strategy30.
  Axiom wnaf3_precomp_points_strategy31_correctness : wnaf3_precomp_points_strategy31.
  Axiom wnaf3_precomp_points_strategy32_correctness : wnaf3_precomp_points_strategy32.
  Axiom wnaf3_precomp_points_strategy33_correctness : wnaf3_precomp_points_strategy33.
  Axiom wnaf3_precomp_points_strategy35_correctness : wnaf3_precomp_points_strategy35.
  Axiom wnaf3_precomp_points_strategy41_correctness : wnaf3_precomp_points_strategy41.
  Axiom wnaf3_precomp_points_strategy42_correctness : wnaf3_precomp_points_strategy42.
  Axiom wnaf3_precomp_points_strategy43_correctness : wnaf3_precomp_points_strategy43.

End wnaf3_precomp_points_Strategy_Correct.
