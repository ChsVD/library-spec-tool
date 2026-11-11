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

Definition ecc_point_copy_steps_strategy10 :=
  forall (p : Z),
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((p)) # "AFPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((p)) # "AFPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 &( ((p)) # "AFPoint" ->ₛ "x"))) **
    ((UndefStructPredu32 &( ((p)) # "AFPoint" ->ₛ "y")))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy15 :=
  forall (p : Z),
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 &( ((p)) # "JPoint" ->ₛ "x"))) **
    ((UndefStructPredu32 &( ((p)) # "JPoint" ->ₛ "y")))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy20 :=
  forall (p : Z),
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "x"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "y"))) # "u32" ->ₛ "v") 4)) **
    ((UInt64Array.undef_full &( ((&( ((p)) # "JPoint" ->ₛ "z"))) # "u32" ->ₛ "v") 4))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredJPoint p))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy25 :=
  forall (p : Z),
    TT &&
    emp **
    ((UndefStructPredJPoint p))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 &( ((p)) # "JPoint" ->ₛ "x"))) **
    ((UndefStructPredu32 &( ((p)) # "JPoint" ->ₛ "y"))) **
    ((UndefStructPredu32 &( ((p)) # "JPoint" ->ₛ "z")))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy30 :=
  forall (result : Z) (point : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (result = point) ”) &&
    emp **
    ((store_jpoint_fields point x y z))
    |--
    (
    TT &&
    (“ (result = point) ”) &&
    emp **
    ((UndefStructPredJPoint result))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy31 :=
  forall (point : Z) (result : Z) (y : Z) (z : Z) (x : Z),
    TT &&
    (“ (point = result) ”) &&
    emp **
    ((store_jpoint_fields point x y z))
    |--
    (
    TT &&
    (“ (point = result) ”) &&
    emp **
    ((UndefStructPredJPoint result))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy32 :=
  forall (result : Z) (point : Z) (y : Z) (x : Z) (z : Z),
    TT &&
    (“ (result = point) ”) &&
    emp **
    ((store_fp &( ((point)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((point)) # "JPoint" ->ₛ "y") y)) **
    ((store_fp &( ((point)) # "JPoint" ->ₛ "z") z))
    |--
    (
    TT &&
    (“ (result = point) ”) &&
    emp **
    ((UndefStructPredJPoint result))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition ecc_point_copy_steps_strategy33 :=
  forall (point : Z) (result : Z) (y : Z) (x : Z) (z : Z),
    TT &&
    (“ (point = result) ”) &&
    emp **
    ((store_fp &( ((point)) # "JPoint" ->ₛ "x") x)) **
    ((store_fp &( ((point)) # "JPoint" ->ₛ "y") y)) **
    ((store_fp &( ((point)) # "JPoint" ->ₛ "z") z))
    |--
    (
    TT &&
    (“ (point = result) ”) &&
    emp **
    ((UndefStructPredJPoint result))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type ecc_point_copy_steps_Strategy_Correct.

  Axiom ecc_point_copy_steps_strategy10_correctness : ecc_point_copy_steps_strategy10.
  Axiom ecc_point_copy_steps_strategy15_correctness : ecc_point_copy_steps_strategy15.
  Axiom ecc_point_copy_steps_strategy20_correctness : ecc_point_copy_steps_strategy20.
  Axiom ecc_point_copy_steps_strategy25_correctness : ecc_point_copy_steps_strategy25.
  Axiom ecc_point_copy_steps_strategy30_correctness : ecc_point_copy_steps_strategy30.
  Axiom ecc_point_copy_steps_strategy31_correctness : ecc_point_copy_steps_strategy31.
  Axiom ecc_point_copy_steps_strategy32_correctness : ecc_point_copy_steps_strategy32.
  Axiom ecc_point_copy_steps_strategy33_correctness : ecc_point_copy_steps_strategy33.

End ecc_point_copy_steps_Strategy_Correct.
