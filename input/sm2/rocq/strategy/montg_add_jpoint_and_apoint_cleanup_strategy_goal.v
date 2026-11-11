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

Definition montg_add_jpoint_and_apoint_cleanup_strategy1 :=
  forall (z2 : Z) (x1 : Z) (x2 : Z) (h : Z) (a : Z) (b : Z) (r : Z) (y2 : Z) (y1 : Z) (tmp : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp a ( mont_p ( maja_u2 x2 z1)))) **
    ((store_fp b ( mont_p ( maja_s2 y2 z1)))) **
    ((store_fp h ( mont_p ( maja_h x1 x2 z1)))) **
    ((store_fp r ( mont_p ( maja_r y1 y2 z1)))) **
    ((store_fp z2 ( mont_p ( maja_z2 z1)))) **
    ((store_fp tmp ( mont_p ( maja_z3 z1))))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 a)) **
    ((UndefStructPredu32 b)) **
    ((UndefStructPredu32 h)) **
    ((UndefStructPredu32 r)) **
    ((UndefStructPredu32 z2)) **
    ((UndefStructPredu32 tmp))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_and_apoint_cleanup_strategy2 :=
  forall (h3 : Z) (e : Z) (h : Z) (a : Z) (b : Z) (r : Z) (z2 : Z) (tmp : Z) (y1 : Z) (x2 : Z) (y2 : Z) (z1 : Z) (x1 : Z),
    TT &&
    emp **
    ((store_fp a ( mont_p ( maja_u2 x2 z1)))) **
    ((store_fp b ( mont_p ( maja_s2 y2 z1)))) **
    ((store_fp h ( mont_p ( maja_h x1 x2 z1)))) **
    ((store_fp r ( mont_p ( maja_r y1 y2 z1)))) **
    ((store_fp e ( mont_p ( maja_u1h2 x1 x2 z1)))) **
    ((store_fp z2 ( mont_p ( maja_z2 z1)))) **
    ((store_fp h3 ( mont_p ( maja_h3 x1 x2 z1)))) **
    ((store_fp tmp ( mont_p ( maja_r_times_delta x1 y1 z1 x2 y2))))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 a)) **
    ((UndefStructPredu32 b)) **
    ((UndefStructPredu32 h)) **
    ((UndefStructPredu32 r)) **
    ((UndefStructPredu32 e)) **
    ((UndefStructPredu32 z2)) **
    ((UndefStructPredu32 h3)) **
    ((UndefStructPredu32 tmp))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type montg_add_jpoint_and_apoint_cleanup_Strategy_Correct.

  Axiom montg_add_jpoint_and_apoint_cleanup_strategy1_correctness : montg_add_jpoint_and_apoint_cleanup_strategy1.
  Axiom montg_add_jpoint_and_apoint_cleanup_strategy2_correctness : montg_add_jpoint_and_apoint_cleanup_strategy2.

End montg_add_jpoint_and_apoint_cleanup_Strategy_Correct.
