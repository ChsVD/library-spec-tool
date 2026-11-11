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

Definition montg_add_jpoint_cleanup_strategy1 :=
  forall (qz2 : Z) (y2 : Z) (s2 : Z) (x2 : Z) (u2 : Z) (u1 : Z) (x1 : Z) (s1 : Z) (y1 : Z) (pz2 : Z) (z1 : Z) (tmp : Z) (z2 : Z),
    TT &&
    emp **
    ((store_fp u1 ( mont_p ( aj_u1 x1 z2)))) **
    ((store_fp u2 ( mont_p ( aj_u2 x2 z1)))) **
    ((store_fp s1 ( mont_p ( aj_s1 y1 z2)))) **
    ((store_fp s2 ( mont_p ( aj_s2 y2 z1)))) **
    ((store_fp pz2 ( mont_p ( aj_pz2 z1)))) **
    ((store_fp qz2 ( mont_p ( aj_qz2 z2)))) **
    ((store_fp tmp ( mont_p ( aj_qz3 z2))))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 u1)) **
    ((UndefStructPredu32 u2)) **
    ((UndefStructPredu32 s1)) **
    ((UndefStructPredu32 s2)) **
    ((UndefStructPredu32 pz2)) **
    ((UndefStructPredu32 qz2)) **
    ((UndefStructPredu32 tmp))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition montg_add_jpoint_cleanup_strategy2 :=
  forall (x1 : Z) (x2 : Z) (h2 : Z) (pz2 : Z) (ssum : Z) (rr : Z) (s1 : Z) (u2 : Z) (u1 : Z) (h : Z) (s2 : Z) (usum : Z) (bmx : Z) (y1 : Z) (y2 : Z) (qz2 : Z) (zbase : Z) (z2 : Z) (z1 : Z),
    TT &&
    emp **
    ((store_fp u1 ( mont_p ( aj_u1 x1 z2)))) **
    ((store_fp u2 ( mont_p ( aj_u2 x2 z1)))) **
    ((store_fp h ( mont_p ( aj_h x1 z1 x2 z2)))) **
    ((store_fp s1 ( mont_p ( aj_s1 y1 z2)))) **
    ((store_fp s2 ( mont_p ( aj_s2 y2 z1)))) **
    ((store_fp rr ( mont_p ( aj_rr y1 z1 y2 z2)))) **
    ((store_fp usum ( mont_p ( aj_u_sum x1 z1 x2 z2)))) **
    ((store_fp ssum ( mont_p ( aj_s_sum y1 z1 y2 z2)))) **
    ((store_fp bmx ( mont_p ( aj_base_minus_twice_rx x1 y1 z1 x2 y2 z2)))) **
    ((store_fp pz2 ( mont_p ( aj_pz2 z1)))) **
    ((store_fp qz2 ( mont_p ( aj_qz2 z2)))) **
    ((store_fp h2 ( mont_p ( aj_h2 x1 z1 x2 z2)))) **
    ((store_fp zbase ( mont_p ( aj_zbase z1 z2))))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 u1)) **
    ((UndefStructPredu32 u2)) **
    ((UndefStructPredu32 h)) **
    ((UndefStructPredu32 s1)) **
    ((UndefStructPredu32 s2)) **
    ((UndefStructPredu32 rr)) **
    ((UndefStructPredu32 usum)) **
    ((UndefStructPredu32 ssum)) **
    ((UndefStructPredu32 bmx)) **
    ((UndefStructPredu32 pz2)) **
    ((UndefStructPredu32 qz2)) **
    ((UndefStructPredu32 h2)) **
    ((UndefStructPredu32 zbase))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type montg_add_jpoint_cleanup_Strategy_Correct.

  Axiom montg_add_jpoint_cleanup_strategy1_correctness : montg_add_jpoint_cleanup_strategy1.
  Axiom montg_add_jpoint_cleanup_strategy2_correctness : montg_add_jpoint_cleanup_strategy2.

End montg_add_jpoint_cleanup_Strategy_Correct.
