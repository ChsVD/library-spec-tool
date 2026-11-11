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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition add_JPoint_boundary_strategy20 :=
  forall (x1 : Z) (z1 : Z) (y2 : Z) (z2 : Z) (x2 : Z) (y1 : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( aj_rx x1 y1 z1 x2 y2 z2)))
    |--
    EX (xs : (@list Z)),
      (
      TT &&
      (“ (Z.le 0 ( aj_rx x1 y1 z1 x2 y2 z2)) ”) &&
      (“ (Z.lt ( aj_rx x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z xs) = 4) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = ( aj_rx x1 y1 z1 x2 y2 z2)) ”) &&
      emp **
      ((UInt64Array.full &( ((p)) # "u32" ->ₛ "v") 4 xs))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition add_JPoint_boundary_strategy21 :=
  forall (x1 : Z) (z1 : Z) (y2 : Z) (z2 : Z) (x2 : Z) (y1 : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( aj_ry x1 y1 z1 x2 y2 z2)))
    |--
    EX (xs : (@list Z)),
      (
      TT &&
      (“ (Z.le 0 ( aj_ry x1 y1 z1 x2 y2 z2)) ”) &&
      (“ (Z.lt ( aj_ry x1 y1 z1 x2 y2 z2) ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z xs) = 4) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = ( aj_ry x1 y1 z1 x2 y2 z2)) ”) &&
      emp **
      ((UInt64Array.full &( ((p)) # "u32" ->ₛ "v") 4 xs))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition add_JPoint_boundary_strategy22 :=
  forall (x1 : Z) (x2 : Z) (z2 : Z) (z1 : Z) (p : Z),
    TT &&
    emp **
    ((store_fp p ( aj_rz x1 z1 x2 z2)))
    |--
    EX (xs : (@list Z)),
      (
      TT &&
      (“ (Z.le 0 ( aj_rz x1 z1 x2 z2)) ”) &&
      (“ (Z.lt ( aj_rz x1 z1 x2 z2) ( SM2_P_Z)) ”) &&
      (“ ((@Zlength Z xs) = 4) ”) &&
      (“ (u64_list_bounded xs) ”) &&
      (“ (( u64_list_value xs) = ( aj_rz x1 z1 x2 z2)) ”) &&
      emp **
      ((UInt64Array.full &( ((p)) # "u32" ->ₛ "v") 4 xs))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Module Type add_JPoint_boundary_Strategy_Correct.

  Axiom add_JPoint_boundary_strategy20_correctness : add_JPoint_boundary_strategy20.
  Axiom add_JPoint_boundary_strategy21_correctness : add_JPoint_boundary_strategy21.
  Axiom add_JPoint_boundary_strategy22_correctness : add_JPoint_boundary_strategy22.

End add_JPoint_boundary_Strategy_Correct.
