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
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sm2_protocol_views_strategy1 :=
  forall (p : Z) (q : Z) (d : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_private_key p d))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_d : Z),
      TT &&
      (“ (d = required_d) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sm2_private_key q required_d))
      ).

Definition sm2_protocol_views_strategy2 :=
  forall (p : Z) (q : Z) (d : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_private_key p d))
    |--
    (
    TT &&
    (“ (valid_sm2_private_key d) ”) &&
    emp
    ) ** (
    ALL (required_d : Z),
      TT &&
      (“ (d = required_d) ”) &&
      emp -*
      TT &&
      emp **
      ((store_fn &( ((q)) # "PrivKey" ->ₛ "da") required_d))
      ).

Definition sm2_protocol_views_strategy4 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((undef_sm2_private_key p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((undef_sm2_private_key q))
    ).

Definition sm2_protocol_views_strategy5 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((undef_sm2_private_key p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UndefStructPredu32 &( ((q)) # "PrivKey" ->ₛ "da")))
    ).

Definition sm2_protocol_views_strategy7 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((undef_sm2_private_key p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full &( ((&( ((q)) # "PrivKey" ->ₛ "da"))) # "u32" ->ₛ "v") 4))
    ).

Definition sm2_protocol_views_strategy10 :=
  forall (p : Z) (q : Z) (s : Z) (r : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_signature p r s))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_s : Z) (required_r : Z),
      TT &&
      (“ (r = required_r) ”) &&
      (“ (s = required_s) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sm2_signature q required_r required_s))
      ).

Definition sm2_protocol_views_strategy11 :=
  forall (p : Z) (q : Z) (s : Z) (r : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_signature p r s))
    |--
    (
    TT &&
    emp **
    ((store_u256 &( ((p)) # "SM2SIG" ->ₛ "s") s))
    ) ** (
    ALL (required_r : Z),
      TT &&
      (“ (r = required_r) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((q)) # "SM2SIG" ->ₛ "r") required_r))
      ).

Definition sm2_protocol_views_strategy12 :=
  forall (p : Z) (q : Z) (s : Z) (r : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_signature p r s))
    |--
    (
    TT &&
    emp **
    ((store_u256 &( ((p)) # "SM2SIG" ->ₛ "r") r))
    ) ** (
    ALL (required_s : Z),
      TT &&
      (“ (s = required_s) ”) &&
      emp -*
      TT &&
      emp **
      ((store_u256 &( ((q)) # "SM2SIG" ->ₛ "s") required_s))
      ).

Definition sm2_protocol_views_strategy14 :=
  forall (p : Z) (q : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((undef_sm2_signature p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((undef_sm2_signature q))
    ).

Definition sm2_protocol_views_strategy20 :=
  forall (p : Z) (q : Z) (point : ec_point),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_public_key p point))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_point : ec_point),
      TT &&
      (“ (point = required_point) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sm2_public_key q required_point))
      ).

Definition sm2_protocol_views_strategy21 :=
  forall (p : Z) (q : Z) (point : ec_point),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_public_key p point))
    |--
    (
    TT &&
    (“ (valid_sm2_public_key point) ”) &&
    emp
    ) ** (
    ALL (required_point : ec_point),
      TT &&
      (“ (point = required_point) ”) &&
      emp -*
      TT &&
      emp **
      ((store_afpoint q required_point))
      ).

Definition sm2_protocol_views_strategy30 :=
  forall (p : Z) (q : Z) (point : ec_point) (za : (@list Z)) (id_bytes : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_za p id_bytes point za))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (required_za : (@list Z)) (required_id : (@list Z)) (required_point : ec_point),
      TT &&
      (“ (id_bytes = required_id) ”) &&
      (“ (point = required_point) ”) &&
      (“ (za = required_za) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sm2_za q required_id required_point required_za))
      ).

Definition sm2_protocol_views_strategy31 :=
  forall (p : Z) (q : Z) (point : ec_point) (id_bytes : (@list Z)) (za : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((store_sm2_za p id_bytes point za))
    |--
    (
    TT &&
    (“ (za = ( sm2_za_digest id_bytes point)) ”) &&
    emp
    ) ** (
    ALL (required_za : (@list Z)),
      TT &&
      (“ (za = required_za) ”) &&
      emp -*
      TT &&
      emp **
      ((store_bytes q 32 required_za))
      ).

Definition sm2_protocol_views_strategy40 :=
  TT &&
  emp **
  ((store_sm2_get_public_key_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_get_public_key_globals))
  ).

Definition sm2_protocol_views_strategy50 :=
  TT &&
  emp **
  ((store_sm2_keypair_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_keypair_globals))
  ).

Definition sm2_protocol_views_strategy60 :=
  TT &&
  emp **
  ((store_sm2_za_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_za_globals))
  ).

Definition sm2_protocol_views_strategy63 :=
  TT &&
  emp **
  ((store_sm2_g))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_g))
  ).

Definition sm2_protocol_views_strategy70 :=
  TT &&
  emp **
  ((store_sm2_sign_dgst_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_sign_dgst_globals))
  ).

Definition sm2_protocol_views_strategy80 :=
  TT &&
  emp **
  ((store_sm2_sign_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_sign_globals))
  ).

Definition sm2_protocol_views_strategy90 :=
  TT &&
  emp **
  ((store_sm2_verify_dgst_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_verify_dgst_globals))
  ).

Definition sm2_protocol_views_strategy100 :=
  TT &&
  emp **
  ((store_sm2_verify_globals))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_verify_globals))
  ).

Definition sm2_protocol_views_strategy15 :=
  forall (p : Z),
    TT &&
    emp **
    ((undef_sm2_signature p))
    |--
    (
    TT &&
    emp **
    ((UndefStructPredu32 &( ((p)) # "SM2SIG" ->ₛ "r"))) **
    ((UndefStructPredu32 &( ((p)) # "SM2SIG" ->ₛ "s")))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_protocol_views_strategy23 :=
  forall (point : ec_point) (p : Z),
    TT &&
    emp **
    ((store_sm2_public_key p point))
    |--
    (
    TT &&
    (“ (valid_sm2_public_key point) ”) &&
    emp **
    ((store_afpoint p point))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_protocol_views_strategy24 :=
  forall (y : Z) (point : ec_point) (x : Z),
    TT &&
    (“ (afpoint_represents x y point) ”) &&
    emp
    |--
    (
    TT &&
    (“ (afpoint_represents x y point) ”) &&
    (“ (x = ( sm2_point_x point)) ”) &&
    (“ (y = ( sm2_point_y point)) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition sm2_protocol_views_strategy41 :=
  TT &&
  emp **
  ((store_sm2_get_public_key_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_jpoint_zero)) **
  ((store_sm2_inv2p))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy51 :=
  TT &&
  emp **
  ((store_sm2_keypair_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_jpoint_zero)) **
  ((store_sm2_inv2p))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy61 :=
  TT &&
  emp **
  ((store_sm2_za_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_g)) **
  ((store_sm3_ti))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy64 :=
  TT &&
  emp **
  ((store_sm2_g))
  |--
  (
  TT &&
  emp **
  ((store_afpoint  &("SM2_G")  ( SM2_G_POINT)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy71 :=
  TT &&
  emp **
  ((store_sm2_sign_dgst_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_nh)) **
  ((store_sm2_neg_inv_n)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_bn_zero)) **
  ((store_montg_one))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy81 :=
  TT &&
  emp **
  ((store_sm2_sign_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_g)) **
  ((store_sm3_ti)) **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_nh)) **
  ((store_sm2_neg_inv_n)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_bn_zero)) **
  ((store_montg_one))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy91 :=
  TT &&
  emp **
  ((store_sm2_verify_dgst_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_h)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_jpoint_zero)) **
  ((store_bn_zero)) **
  ((store_montg_one))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy101 :=
  TT &&
  emp **
  ((store_sm2_verify_globals))
  |--
  (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_h)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_jpoint_zero)) **
  ((store_bn_zero)) **
  ((store_montg_one)) **
  ((store_sm2_g)) **
  ((store_sm3_ti))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_protocol_views_strategy3 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (d : Z) (p : Z),
    TT &&
    (“ (valid_sm2_private_key d) ”) &&
    emp **
    ((store_fn &( ((p)) # "PrivKey" ->ₛ "da") d)) -*
    TT &&
    emp **
    ((store_sm2_private_key p d))
    ).

Definition sm2_protocol_views_strategy6 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    emp **
    ((UndefStructPredu32 &( ((p)) # "PrivKey" ->ₛ "da"))) -*
    TT &&
    emp **
    ((undef_sm2_private_key p))
    ).

Definition sm2_protocol_views_strategy13 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (r : Z) (p : Z) (s : Z),
    TT &&
    emp **
    ((store_u256 &( ((p)) # "SM2SIG" ->ₛ "r") r)) **
    ((store_u256 &( ((p)) # "SM2SIG" ->ₛ "s") s)) -*
    TT &&
    emp **
    ((store_sm2_signature p r s))
    ).

Definition sm2_protocol_views_strategy16 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    emp **
    ((UndefStructPredu32 &( ((p)) # "SM2SIG" ->ₛ "r"))) **
    ((UndefStructPredu32 &( ((p)) # "SM2SIG" ->ₛ "s"))) -*
    TT &&
    emp **
    ((undef_sm2_signature p))
    ).

Definition sm2_protocol_views_strategy22 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (point : ec_point) (p : Z),
    TT &&
    (“ (valid_sm2_public_key point) ”) &&
    emp **
    ((store_afpoint p point)) -*
    TT &&
    emp **
    ((store_sm2_public_key p point))
    ).

Definition sm2_protocol_views_strategy32 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (za : (@list Z)) (id_bytes : (@list Z)) (point : ec_point) (p : Z),
    TT &&
    (“ (za = ( sm2_za_digest id_bytes point)) ”) &&
    emp **
    ((store_bytes p 32 za)) -*
    TT &&
    emp **
    ((store_sm2_za p id_bytes point za))
    ).

Definition sm2_protocol_views_strategy42 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_jpoint_zero)) **
  ((store_sm2_inv2p)) -*
  TT &&
  emp **
  ((store_sm2_get_public_key_globals))
  ).

Definition sm2_protocol_views_strategy52 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_jpoint_zero)) **
  ((store_sm2_inv2p)) -*
  TT &&
  emp **
  ((store_sm2_keypair_globals))
  ).

Definition sm2_protocol_views_strategy62 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_g)) **
  ((store_sm3_ti)) -*
  TT &&
  emp **
  ((store_sm2_za_globals))
  ).

Definition sm2_protocol_views_strategy65 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_afpoint  &("SM2_G")  ( SM2_G_POINT))) -*
  TT &&
  emp **
  ((store_sm2_g))
  ).

Definition sm2_protocol_views_strategy72 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_nh)) **
  ((store_sm2_neg_inv_n)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_bn_zero)) **
  ((store_montg_one)) -*
  TT &&
  emp **
  ((store_sm2_sign_dgst_globals))
  ).

Definition sm2_protocol_views_strategy82 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_g)) **
  ((store_sm3_ti)) **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_nh)) **
  ((store_sm2_neg_inv_n)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_bn_zero)) **
  ((store_montg_one)) -*
  TT &&
  emp **
  ((store_sm2_sign_globals))
  ).

Definition sm2_protocol_views_strategy92 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_h)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_jpoint_zero)) **
  ((store_bn_zero)) **
  ((store_montg_one)) -*
  TT &&
  emp **
  ((store_sm2_verify_dgst_globals))
  ).

Definition sm2_protocol_views_strategy102 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp **
  ((store_sm2_a)) **
  ((store_sm2_b)) **
  ((store_sm2_n)) **
  ((store_sm2_rhon)) **
  ((store_sm2_h)) **
  ((store_sm2_p)) **
  ((store_sm2_rhop)) **
  ((store_sm2_mont_base_point_table)) **
  ((store_jpoint_zero)) **
  ((store_bn_zero)) **
  ((store_montg_one)) **
  ((store_sm2_g)) **
  ((store_sm3_ti)) -*
  TT &&
  emp **
  ((store_sm2_verify_globals))
  ).

Module Type sm2_protocol_views_Strategy_Correct.

  Axiom sm2_protocol_views_strategy1_correctness : sm2_protocol_views_strategy1.
  Axiom sm2_protocol_views_strategy2_correctness : sm2_protocol_views_strategy2.
  Axiom sm2_protocol_views_strategy4_correctness : sm2_protocol_views_strategy4.
  Axiom sm2_protocol_views_strategy5_correctness : sm2_protocol_views_strategy5.
  Axiom sm2_protocol_views_strategy7_correctness : sm2_protocol_views_strategy7.
  Axiom sm2_protocol_views_strategy10_correctness : sm2_protocol_views_strategy10.
  Axiom sm2_protocol_views_strategy11_correctness : sm2_protocol_views_strategy11.
  Axiom sm2_protocol_views_strategy12_correctness : sm2_protocol_views_strategy12.
  Axiom sm2_protocol_views_strategy14_correctness : sm2_protocol_views_strategy14.
  Axiom sm2_protocol_views_strategy20_correctness : sm2_protocol_views_strategy20.
  Axiom sm2_protocol_views_strategy21_correctness : sm2_protocol_views_strategy21.
  Axiom sm2_protocol_views_strategy30_correctness : sm2_protocol_views_strategy30.
  Axiom sm2_protocol_views_strategy31_correctness : sm2_protocol_views_strategy31.
  Axiom sm2_protocol_views_strategy40_correctness : sm2_protocol_views_strategy40.
  Axiom sm2_protocol_views_strategy50_correctness : sm2_protocol_views_strategy50.
  Axiom sm2_protocol_views_strategy60_correctness : sm2_protocol_views_strategy60.
  Axiom sm2_protocol_views_strategy63_correctness : sm2_protocol_views_strategy63.
  Axiom sm2_protocol_views_strategy70_correctness : sm2_protocol_views_strategy70.
  Axiom sm2_protocol_views_strategy80_correctness : sm2_protocol_views_strategy80.
  Axiom sm2_protocol_views_strategy90_correctness : sm2_protocol_views_strategy90.
  Axiom sm2_protocol_views_strategy100_correctness : sm2_protocol_views_strategy100.
  Axiom sm2_protocol_views_strategy15_correctness : sm2_protocol_views_strategy15.
  Axiom sm2_protocol_views_strategy23_correctness : sm2_protocol_views_strategy23.
  Axiom sm2_protocol_views_strategy24_correctness : sm2_protocol_views_strategy24.
  Axiom sm2_protocol_views_strategy41_correctness : sm2_protocol_views_strategy41.
  Axiom sm2_protocol_views_strategy51_correctness : sm2_protocol_views_strategy51.
  Axiom sm2_protocol_views_strategy61_correctness : sm2_protocol_views_strategy61.
  Axiom sm2_protocol_views_strategy64_correctness : sm2_protocol_views_strategy64.
  Axiom sm2_protocol_views_strategy71_correctness : sm2_protocol_views_strategy71.
  Axiom sm2_protocol_views_strategy81_correctness : sm2_protocol_views_strategy81.
  Axiom sm2_protocol_views_strategy91_correctness : sm2_protocol_views_strategy91.
  Axiom sm2_protocol_views_strategy101_correctness : sm2_protocol_views_strategy101.
  Axiom sm2_protocol_views_strategy3_correctness : sm2_protocol_views_strategy3.
  Axiom sm2_protocol_views_strategy6_correctness : sm2_protocol_views_strategy6.
  Axiom sm2_protocol_views_strategy13_correctness : sm2_protocol_views_strategy13.
  Axiom sm2_protocol_views_strategy16_correctness : sm2_protocol_views_strategy16.
  Axiom sm2_protocol_views_strategy22_correctness : sm2_protocol_views_strategy22.
  Axiom sm2_protocol_views_strategy32_correctness : sm2_protocol_views_strategy32.
  Axiom sm2_protocol_views_strategy42_correctness : sm2_protocol_views_strategy42.
  Axiom sm2_protocol_views_strategy52_correctness : sm2_protocol_views_strategy52.
  Axiom sm2_protocol_views_strategy62_correctness : sm2_protocol_views_strategy62.
  Axiom sm2_protocol_views_strategy65_correctness : sm2_protocol_views_strategy65.
  Axiom sm2_protocol_views_strategy72_correctness : sm2_protocol_views_strategy72.
  Axiom sm2_protocol_views_strategy82_correctness : sm2_protocol_views_strategy82.
  Axiom sm2_protocol_views_strategy92_correctness : sm2_protocol_views_strategy92.
  Axiom sm2_protocol_views_strategy102_correctness : sm2_protocol_views_strategy102.

End sm2_protocol_views_Strategy_Correct.
