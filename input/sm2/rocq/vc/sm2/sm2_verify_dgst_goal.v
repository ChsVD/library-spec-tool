Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_verify_dgst -----*)

Definition sm2_verify_dgst_safety_wit_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ~((valid_afpoint x y ))) (PreH5 : (valid_afpoint x y )) (PreH6 : (afpoint_represents x y P_verifies )) (PreH7 : ((u64_list_value (zs)) = 0)) (PreH8 : (u64_list_bounded zs )) (PreH9 : ((Zlength (zs)) = 4)) (PreH10 : (0 < SM2_P_Z)) (PreH11 : (0 <= 0)) (PreH12 : ((u64_list_value (ys)) = 1)) (PreH13 : (u64_list_bounded ys )) (PreH14 : ((Zlength (ys)) = 4)) (PreH15 : (1 < SM2_P_Z)) (PreH16 : (0 <= 1)) (PreH17 : ((u64_list_value (xs)) = 1)) (PreH18 : (u64_list_bounded xs )) (PreH19 : ((Zlength (xs)) = 4)) (PreH20 : (1 < SM2_P_Z)) (PreH21 : (0 <= 1)) (PreH22 : (P_verifies <> ECInfinity)) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_verifies )) (PreH8 : ((u64_list_value (zs)) = 0)) (PreH9 : (u64_list_bounded zs )) (PreH10 : ((Zlength (zs)) = 4)) (PreH11 : (0 < SM2_P_Z)) (PreH12 : (0 <= 0)) (PreH13 : ((u64_list_value (ys)) = 1)) (PreH14 : (u64_list_bounded ys )) (PreH15 : ((Zlength (ys)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : ((u64_list_value (xs)) = 1)) (PreH19 : (u64_list_bounded xs )) (PreH20 : ((Zlength (xs)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : (P_verifies <> ECInfinity)) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_3 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (SigR_verifies = 0)) (PreH5 : (retval_2 = 0)) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 1)) (PreH9 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (retval <> 0)) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1)) (PreH13 : (retval = 1)) (PreH14 : (valid_afpoint x y )) (PreH15 : (valid_afpoint x y )) (PreH16 : (afpoint_represents x y P_verifies )) (PreH17 : ((u64_list_value (zs)) = 0)) (PreH18 : (u64_list_bounded zs )) (PreH19 : ((Zlength (zs)) = 4)) (PreH20 : (0 < SM2_P_Z)) (PreH21 : (0 <= 0)) (PreH22 : ((u64_list_value (ys)) = 1)) (PreH23 : (u64_list_bounded ys )) (PreH24 : ((Zlength (ys)) = 4)) (PreH25 : (1 < SM2_P_Z)) (PreH26 : (0 <= 1)) (PreH27 : ((u64_list_value (xs)) = 1)) (PreH28 : (u64_list_bounded xs )) (PreH29 : ((Zlength (xs)) = 4)) (PreH30 : (1 < SM2_P_Z)) (PreH31 : (0 <= 1)) (PreH32 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_4 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (SigR_verifies <> 0)) (PreH5 : (retval_2 = 0)) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 1)) (PreH9 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (retval <> 0)) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1)) (PreH13 : (retval = 1)) (PreH14 : (valid_afpoint x y )) (PreH15 : (valid_afpoint x y )) (PreH16 : (afpoint_represents x y P_verifies )) (PreH17 : ((u64_list_value (zs)) = 0)) (PreH18 : (u64_list_bounded zs )) (PreH19 : ((Zlength (zs)) = 4)) (PreH20 : (0 < SM2_P_Z)) (PreH21 : (0 <= 0)) (PreH22 : ((u64_list_value (ys)) = 1)) (PreH23 : (u64_list_bounded ys )) (PreH24 : ((Zlength (ys)) = 4)) (PreH25 : (1 < SM2_P_Z)) (PreH26 : (0 <= 1)) (PreH27 : ((u64_list_value (xs)) = 1)) (PreH28 : (u64_list_bounded xs )) (PreH29 : ((Zlength (xs)) = 4)) (PreH30 : (1 < SM2_P_Z)) (PreH31 : (0 <= 1)) (PreH32 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_5 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 1)) (PreH4 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (retval_3 = 0)) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 <= 1)) (PreH8 : (retval_3 = 1)) (PreH9 : (SigR_verifies = 0)) (PreH10 : (retval_2 = 0)) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1)) (PreH13 : (retval_2 = 0)) (PreH14 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH15 : (retval <> 0)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 1)) (PreH19 : (valid_afpoint x y )) (PreH20 : (valid_afpoint x y )) (PreH21 : (afpoint_represents x y P_verifies )) (PreH22 : ((u64_list_value (zs)) = 0)) (PreH23 : (u64_list_bounded zs )) (PreH24 : ((Zlength (zs)) = 4)) (PreH25 : (0 < SM2_P_Z)) (PreH26 : (0 <= 0)) (PreH27 : ((u64_list_value (ys)) = 1)) (PreH28 : (u64_list_bounded ys )) (PreH29 : ((Zlength (ys)) = 4)) (PreH30 : (1 < SM2_P_Z)) (PreH31 : (0 <= 1)) (PreH32 : ((u64_list_value (xs)) = 1)) (PreH33 : (u64_list_bounded xs )) (PreH34 : ((Zlength (xs)) = 4)) (PreH35 : (1 < SM2_P_Z)) (PreH36 : (0 <= 1)) (PreH37 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_6 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH5 : (retval_3 = 0)) (PreH6 : (0 <= retval_3)) (PreH7 : (retval_3 <= 1)) (PreH8 : (retval_3 = 1)) (PreH9 : (SigR_verifies = 0)) (PreH10 : (retval_2 = 0)) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1)) (PreH13 : (retval_2 = 0)) (PreH14 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH15 : (retval <> 0)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 1)) (PreH19 : (valid_afpoint x y )) (PreH20 : (valid_afpoint x y )) (PreH21 : (afpoint_represents x y P_verifies )) (PreH22 : ((u64_list_value (zs)) = 0)) (PreH23 : (u64_list_bounded zs )) (PreH24 : ((Zlength (zs)) = 4)) (PreH25 : (0 < SM2_P_Z)) (PreH26 : (0 <= 0)) (PreH27 : ((u64_list_value (ys)) = 1)) (PreH28 : (u64_list_bounded ys )) (PreH29 : ((Zlength (ys)) = 4)) (PreH30 : (1 < SM2_P_Z)) (PreH31 : (0 <= 1)) (PreH32 : ((u64_list_value (xs)) = 1)) (PreH33 : (u64_list_bounded xs )) (PreH34 : ((Zlength (xs)) = 4)) (PreH35 : (1 < SM2_P_Z)) (PreH36 : (0 <= 1)) (PreH37 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_7 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (SigS_verifies = 0)) (PreH5 : (retval_4 = 0)) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 <= 1)) (PreH8 : (retval_4 = 1)) (PreH9 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (retval_3 = 0)) (PreH11 : (0 <= retval_3)) (PreH12 : (retval_3 <= 1)) (PreH13 : (retval_3 = 0)) (PreH14 : (SigR_verifies <> 0)) (PreH15 : (retval_2 = 0)) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval <> 0)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (retval = 1)) (PreH24 : (valid_afpoint x y )) (PreH25 : (valid_afpoint x y )) (PreH26 : (afpoint_represents x y P_verifies )) (PreH27 : ((u64_list_value (zs)) = 0)) (PreH28 : (u64_list_bounded zs )) (PreH29 : ((Zlength (zs)) = 4)) (PreH30 : (0 < SM2_P_Z)) (PreH31 : (0 <= 0)) (PreH32 : ((u64_list_value (ys)) = 1)) (PreH33 : (u64_list_bounded ys )) (PreH34 : ((Zlength (ys)) = 4)) (PreH35 : (1 < SM2_P_Z)) (PreH36 : (0 <= 1)) (PreH37 : ((u64_list_value (xs)) = 1)) (PreH38 : (u64_list_bounded xs )) (PreH39 : ((Zlength (xs)) = 4)) (PreH40 : (1 < SM2_P_Z)) (PreH41 : (0 <= 1)) (PreH42 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_8 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (SigS_verifies <> 0)) (PreH5 : (retval_4 = 0)) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 <= 1)) (PreH8 : (retval_4 = 1)) (PreH9 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH10 : (retval_3 = 0)) (PreH11 : (0 <= retval_3)) (PreH12 : (retval_3 <= 1)) (PreH13 : (retval_3 = 0)) (PreH14 : (SigR_verifies <> 0)) (PreH15 : (retval_2 = 0)) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval <> 0)) (PreH21 : (0 <= retval)) (PreH22 : (retval <= 1)) (PreH23 : (retval = 1)) (PreH24 : (valid_afpoint x y )) (PreH25 : (valid_afpoint x y )) (PreH26 : (afpoint_represents x y P_verifies )) (PreH27 : ((u64_list_value (zs)) = 0)) (PreH28 : (u64_list_bounded zs )) (PreH29 : ((Zlength (zs)) = 4)) (PreH30 : (0 < SM2_P_Z)) (PreH31 : (0 <= 0)) (PreH32 : ((u64_list_value (ys)) = 1)) (PreH33 : (u64_list_bounded ys )) (PreH34 : ((Zlength (ys)) = 4)) (PreH35 : (1 < SM2_P_Z)) (PreH36 : (0 <= 1)) (PreH37 : ((u64_list_value (xs)) = 1)) (PreH38 : (u64_list_bounded xs )) (PreH39 : ((Zlength (xs)) = 4)) (PreH40 : (1 < SM2_P_Z)) (PreH41 : (0 <= 1)) (PreH42 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_9 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_10 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 0)) (PreH5 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_11 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_12 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 0)) (PreH5 : (SigR_verifies <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_13 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_14 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_15 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_16 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_17 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_18 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 1)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_19 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 <> 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_20 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 1)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 <> 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_21 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_22 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 <> 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ False ”
.

Definition sm2_verify_dgst_safety_wit_23 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 <> 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_24 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_safety_wit_25 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_dgst_entail_wit_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (PreH1 : (P_verifies <> ECInfinity)) ,
  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
|--
  “ (P_verifies <> ECInfinity) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
.

Definition sm2_verify_dgst_entail_wit_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (PreH1 : (P_verifies <> ECInfinity)) ,
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ (P_verifies <> ECInfinity) ”
  &&  (store_jpoint_fields ( &( "JPoint_ZERO" ) ) 1 1 0 )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
.

Definition sm2_verify_dgst_entail_wit_3 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (PreH1 : (P_verifies <> ECInfinity)) ,
  (store_jpoint_fields ( &( "JPoint_ZERO" ) ) 1 1 0 )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  EX (zs: (@list Z))  (ys: (@list Z))  (xs: (@list Z)) ,
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
.

Definition sm2_verify_dgst_entail_wit_4 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  EX (y: Z)  (x: Z) ,
  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_afpoint_fields pubkey_pre x y )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_5 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (PreH1 : (afpoint_represents x y P_verifies )) (PreH2 : ((u64_list_value (zs)) = 0)) (PreH3 : (u64_list_bounded zs )) (PreH4 : ((Zlength (zs)) = 4)) (PreH5 : (0 < SM2_P_Z)) (PreH6 : (0 <= 0)) (PreH7 : ((u64_list_value (ys)) = 1)) (PreH8 : (u64_list_bounded ys )) (PreH9 : ((Zlength (ys)) = 4)) (PreH10 : (1 < SM2_P_Z)) (PreH11 : (0 <= 1)) (PreH12 : ((u64_list_value (xs)) = 1)) (PreH13 : (u64_list_bounded xs )) (PreH14 : ((Zlength (xs)) = 4)) (PreH15 : (1 < SM2_P_Z)) (PreH16 : (0 <= 1)) (PreH17 : (P_verifies <> ECInfinity)) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_afpoint_fields pubkey_pre x y )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_6 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_verifies )) (PreH8 : ((u64_list_value (zs)) = 0)) (PreH9 : (u64_list_bounded zs )) (PreH10 : ((Zlength (zs)) = 4)) (PreH11 : (0 < SM2_P_Z)) (PreH12 : (0 <= 0)) (PreH13 : ((u64_list_value (ys)) = 1)) (PreH14 : (u64_list_bounded ys )) (PreH15 : ((Zlength (ys)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : ((u64_list_value (xs)) = 1)) (PreH19 : (u64_list_bounded xs )) (PreH20 : ((Zlength (xs)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : (P_verifies <> ECInfinity)) ,
  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_7_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_7_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : (0 <= retval_6)) (PreH3 : (retval_6 <= 1)) (PreH4 : (retval_6 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  EX (retval_5: Z) ,
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_8_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_8_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_7: Z) (PreH1 : (retval_7 <> 0)) (PreH2 : (0 <= retval_7)) (PreH3 : (retval_7 <= 1)) (PreH4 : (retval_7 = 0)) (PreH5 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_5: Z) ,
  “ (retval_5 <> 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 1) ” 
  &&  “ (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ (SigR_verifies = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_8: Z) ,
  “ (retval_8 <> 0) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ (SigS_verifies = 0) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
.

Definition sm2_verify_dgst_entail_wit_8_3 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_5: Z) ,
  “ (retval_5 <> 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 1) ” 
  &&  “ (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ (SigR_verifies = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_8: Z)  (retval_7: Z)  (retval_3: Z) ,
  “ (retval_8 <> 0) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ (SigS_verifies = 0) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
.

Definition sm2_verify_dgst_entail_wit_8_4 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_5 <> 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 1) ” 
  &&  “ (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_8_5 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 0)) (PreH5 : (SigR_verifies <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_5: Z) ,
  “ (retval_5 <> 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 1) ” 
  &&  “ (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ (SigR_verifies = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_8: Z)  (retval_7: Z) ,
  “ (retval_8 <> 0) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ (SigS_verifies = 0) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
.

Definition sm2_verify_dgst_entail_wit_8_6 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (0 <= retval_6)) (PreH3 : (retval_6 <= 1)) (PreH4 : (retval_6 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ (SigR_verifies = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_8_7 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_7: Z) (retval_9: Z) (PreH1 : (retval_9 <> 0)) (PreH2 : (0 <= retval_9)) (PreH3 : (retval_9 <= 1)) (PreH4 : (retval_9 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_7 = 0)) (PreH7 : (0 <= retval_7)) (PreH8 : (retval_7 <= 1)) (PreH9 : (retval_7 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_5: Z) ,
  “ (retval_5 <> 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 1) ” 
  &&  “ (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ (SigR_verifies = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
  ||
  (EX (retval_8: Z) ,
  “ (retval_8 <> 0) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ (SigS_verifies = 0) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies ))
.

Definition sm2_verify_dgst_entail_wit_8_8 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 <> 0)) (PreH2 : (0 <= retval_8)) (PreH3 : (retval_8 <= 1)) (PreH4 : (retval_8 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_7 = 0)) (PreH7 : (0 <= retval_7)) (PreH8 : (retval_7 <= 1)) (PreH9 : (retval_7 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_8 <> 0) ” 
  &&  “ (0 <= retval_8) ” 
  &&  “ (retval_8 <= 1) ” 
  &&  “ (retval_8 = 1) ” 
  &&  “ (SigS_verifies = 0) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (0 <= retval_7) ” 
  &&  “ (retval_7 <= 1) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_9_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_7: Z) (PreH1 : (0 <= retval_7)) (PreH2 : (retval_7 <= 1)) (PreH3 : (retval_7 = 1)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_7 = 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  EX (retval_6: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_9_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_10_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 1)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 <> 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_10_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_7: Z) (PreH1 : (0 <= retval_7)) (PreH2 : (retval_7 <= 1)) (PreH3 : (retval_7 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_7 <> 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  EX (retval_6: Z) ,
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 <> 0) ”
  &&  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_entail_wit_11_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_entail_wit_11_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_9 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  EX (retval_8: Z) ,
  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_entail_wit_12_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_9: Z) (PreH1 : (retval_9 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_9 <> 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  EX (retval_8: Z) ,
  “ (retval_8 = 1) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_entail_wit_12_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 <> 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  “ (retval_8 = 1) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 <> 0) ”
  &&  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_entail_wit_13 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : (0 = 0)) (PreH3 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH4 : (retval_8 = 0)) (PreH5 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH6 : (retval_7 = 1)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH13 : (retval_5 = 0)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (SigS_verifies <> 0)) (PreH18 : (retval_4 = 0)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (retval_4 = 0)) (PreH22 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH23 : (retval_3 = 0)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (retval_3 = 0)) (PreH27 : (SigR_verifies <> 0)) (PreH28 : (retval_2 = 0)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH33 : (retval <> 0)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (retval = 1)) (PreH37 : (valid_afpoint x y )) (PreH38 : (valid_afpoint x y )) (PreH39 : (afpoint_represents x y P_verifies )) (PreH40 : ((u64_list_value (zs)) = 0)) (PreH41 : (u64_list_bounded zs )) (PreH42 : ((Zlength (zs)) = 4)) (PreH43 : (0 < SM2_P_Z)) (PreH44 : (0 <= 0)) (PreH45 : ((u64_list_value (ys)) = 1)) (PreH46 : (u64_list_bounded ys )) (PreH47 : ((Zlength (ys)) = 4)) (PreH48 : (1 < SM2_P_Z)) (PreH49 : (0 <= 1)) (PreH50 : ((u64_list_value (xs)) = 1)) (PreH51 : (u64_list_bounded xs )) (PreH52 : ((Zlength (xs)) = 4)) (PreH53 : (1 < SM2_P_Z)) (PreH54 : (0 <= 1)) (PreH55 : (P_verifies <> ECInfinity)) (PreH56 : (retval_6 = 0)) (PreH57 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_u256_limbs (&(( &( "t" ) )->ₛ "v") + (0 * sizeof(UINT64))) RX )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (retval_9 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) ) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 ( &( "t" ) ) RX )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
.

Definition sm2_verify_dgst_return_wit_1 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = SigR_verifies)) (PreH5 : (SigR_verifies < SM2_N_Z)) (PreH6 : (0 <= SigR_verifies)) (PreH7 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH8 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH9 : (retval_10 = 1)) (PreH10 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH11 : (retval_9 = 0)) (PreH12 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH13 : (retval_8 = 1)) (PreH14 : (0 <= retval_7)) (PreH15 : (retval_7 <= 1)) (PreH16 : (retval_7 = 0)) (PreH17 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH18 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH19 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH20 : (retval_6 = 0)) (PreH21 : (0 <= retval_6)) (PreH22 : (retval_6 <= 1)) (PreH23 : (retval_6 = 0)) (PreH24 : (SigS_verifies <> 0)) (PreH25 : (retval_5 = 0)) (PreH26 : (0 <= retval_5)) (PreH27 : (retval_5 <= 1)) (PreH28 : (retval_5 = 0)) (PreH29 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval_4 = 0)) (PreH31 : (0 <= retval_4)) (PreH32 : (retval_4 <= 1)) (PreH33 : (retval_4 = 0)) (PreH34 : (SigR_verifies <> 0)) (PreH35 : (retval_3 = 0)) (PreH36 : (0 <= retval_3)) (PreH37 : (retval_3 <= 1)) (PreH38 : (retval_3 = 0)) (PreH39 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH40 : (retval_2 <> 0)) (PreH41 : (0 <= retval_2)) (PreH42 : (retval_2 <= 1)) (PreH43 : (retval_2 = 1)) (PreH44 : (valid_afpoint x y )) (PreH45 : (valid_afpoint x y )) (PreH46 : (afpoint_represents x y P_verifies )) (PreH47 : ((u64_list_value (zs)) = 0)) (PreH48 : (u64_list_bounded zs )) (PreH49 : ((Zlength (zs)) = 4)) (PreH50 : (0 < SM2_P_Z)) (PreH51 : (0 <= 0)) (PreH52 : ((u64_list_value (ys)) = 1)) (PreH53 : (u64_list_bounded ys )) (PreH54 : ((Zlength (ys)) = 4)) (PreH55 : (1 < SM2_P_Z)) (PreH56 : (0 <= 1)) (PreH57 : ((u64_list_value (xs)) = 1)) (PreH58 : (u64_list_bounded xs )) (PreH59 : ((Zlength (xs)) = 4)) (PreH60 : (1 < SM2_P_Z)) (PreH61 : (0 <= 1)) (PreH62 : (P_verifies <> ECInfinity)) (PreH63 : (retval_7 = 0)) (PreH64 : (retval_9 = 0)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies ) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = SigR_verifies)) (PreH7 : (SigR_verifies < SM2_N_Z)) (PreH8 : (0 <= SigR_verifies)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH11 : (retval_10 = 1)) (PreH12 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH13 : (retval_9 = 0)) (PreH14 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH15 : (retval_8 = 1)) (PreH16 : (0 <= retval_7)) (PreH17 : (retval_7 <= 1)) (PreH18 : (retval_7 = 0)) (PreH19 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH20 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH21 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH22 : (retval_6 = 0)) (PreH23 : (0 <= retval_6)) (PreH24 : (retval_6 <= 1)) (PreH25 : (retval_6 = 0)) (PreH26 : (SigS_verifies <> 0)) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= retval_5)) (PreH29 : (retval_5 <= 1)) (PreH30 : (retval_5 = 0)) (PreH31 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval_4 = 0)) (PreH33 : (0 <= retval_4)) (PreH34 : (retval_4 <= 1)) (PreH35 : (retval_4 = 0)) (PreH36 : (SigR_verifies <> 0)) (PreH37 : (retval_3 = 0)) (PreH38 : (0 <= retval_3)) (PreH39 : (retval_3 <= 1)) (PreH40 : (retval_3 = 0)) (PreH41 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH42 : (retval_2 <> 0)) (PreH43 : (0 <= retval_2)) (PreH44 : (retval_2 <= 1)) (PreH45 : (retval_2 = 1)) (PreH46 : (valid_afpoint x y )) (PreH47 : (valid_afpoint x y )) (PreH48 : (afpoint_represents x y P_verifies )) (PreH49 : ((u64_list_value (zs)) = 0)) (PreH50 : (u64_list_bounded zs )) (PreH51 : ((Zlength (zs)) = 4)) (PreH52 : (0 < SM2_P_Z)) (PreH53 : (0 <= 0)) (PreH54 : ((u64_list_value (ys)) = 1)) (PreH55 : (u64_list_bounded ys )) (PreH56 : ((Zlength (ys)) = 4)) (PreH57 : (1 < SM2_P_Z)) (PreH58 : (0 <= 1)) (PreH59 : ((u64_list_value (xs)) = 1)) (PreH60 : (u64_list_bounded xs )) (PreH61 : ((Zlength (xs)) = 4)) (PreH62 : (1 < SM2_P_Z)) (PreH63 : (0 <= 1)) (PreH64 : (P_verifies <> ECInfinity)) (PreH65 : (retval_7 = 0)) (PreH66 : (retval_9 = 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies ) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_1_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = SigR_verifies)) (PreH7 : (SigR_verifies < SM2_N_Z)) (PreH8 : (0 <= SigR_verifies)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH11 : (retval_10 = 1)) (PreH12 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH13 : (retval_9 = 0)) (PreH14 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH15 : (retval_8 = 1)) (PreH16 : (0 <= retval_7)) (PreH17 : (retval_7 <= 1)) (PreH18 : (retval_7 = 0)) (PreH19 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH20 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH21 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH22 : (retval_6 = 0)) (PreH23 : (0 <= retval_6)) (PreH24 : (retval_6 <= 1)) (PreH25 : (retval_6 = 0)) (PreH26 : (SigS_verifies <> 0)) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= retval_5)) (PreH29 : (retval_5 <= 1)) (PreH30 : (retval_5 = 0)) (PreH31 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval_4 = 0)) (PreH33 : (0 <= retval_4)) (PreH34 : (retval_4 <= 1)) (PreH35 : (retval_4 = 0)) (PreH36 : (SigR_verifies <> 0)) (PreH37 : (retval_3 = 0)) (PreH38 : (0 <= retval_3)) (PreH39 : (retval_3 <= 1)) (PreH40 : (retval_3 = 0)) (PreH41 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH42 : (retval_2 <> 0)) (PreH43 : (0 <= retval_2)) (PreH44 : (retval_2 <= 1)) (PreH45 : (retval_2 = 1)) (PreH46 : (valid_afpoint x y )) (PreH47 : (valid_afpoint x y )) (PreH48 : (afpoint_represents x y P_verifies )) (PreH49 : ((u64_list_value (zs)) = 0)) (PreH50 : (u64_list_bounded zs )) (PreH51 : ((Zlength (zs)) = 4)) (PreH52 : (0 < SM2_P_Z)) (PreH53 : (0 <= 0)) (PreH54 : ((u64_list_value (ys)) = 1)) (PreH55 : (u64_list_bounded ys )) (PreH56 : ((Zlength (ys)) = 4)) (PreH57 : (1 < SM2_P_Z)) (PreH58 : (0 <= 1)) (PreH59 : ((u64_list_value (xs)) = 1)) (PreH60 : (u64_list_bounded xs )) (PreH61 : ((Zlength (xs)) = 4)) (PreH62 : (1 < SM2_P_Z)) (PreH63 : (0 <= 1)) (PreH64 : (P_verifies <> ECInfinity)) (PreH65 : (retval_7 = 0)) (PreH66 : (retval_9 = 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies ) ”
.

Definition sm2_verify_dgst_return_wit_1_split_goal_spatial := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = SigR_verifies)) (PreH7 : (SigR_verifies < SM2_N_Z)) (PreH8 : (0 <= SigR_verifies)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH11 : (retval_10 = 1)) (PreH12 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH13 : (retval_9 = 0)) (PreH14 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH15 : (retval_8 = 1)) (PreH16 : (0 <= retval_7)) (PreH17 : (retval_7 <= 1)) (PreH18 : (retval_7 = 0)) (PreH19 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH20 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH21 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH22 : (retval_6 = 0)) (PreH23 : (0 <= retval_6)) (PreH24 : (retval_6 <= 1)) (PreH25 : (retval_6 = 0)) (PreH26 : (SigS_verifies <> 0)) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= retval_5)) (PreH29 : (retval_5 <= 1)) (PreH30 : (retval_5 = 0)) (PreH31 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval_4 = 0)) (PreH33 : (0 <= retval_4)) (PreH34 : (retval_4 <= 1)) (PreH35 : (retval_4 = 0)) (PreH36 : (SigR_verifies <> 0)) (PreH37 : (retval_3 = 0)) (PreH38 : (0 <= retval_3)) (PreH39 : (retval_3 <= 1)) (PreH40 : (retval_3 = 0)) (PreH41 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH42 : (retval_2 <> 0)) (PreH43 : (0 <= retval_2)) (PreH44 : (retval_2 <= 1)) (PreH45 : (retval_2 = 1)) (PreH46 : (valid_afpoint x y )) (PreH47 : (valid_afpoint x y )) (PreH48 : (afpoint_represents x y P_verifies )) (PreH49 : ((u64_list_value (zs)) = 0)) (PreH50 : (u64_list_bounded zs )) (PreH51 : ((Zlength (zs)) = 4)) (PreH52 : (0 < SM2_P_Z)) (PreH53 : (0 <= 0)) (PreH54 : ((u64_list_value (ys)) = 1)) (PreH55 : (u64_list_bounded ys )) (PreH56 : ((Zlength (ys)) = 4)) (PreH57 : (1 < SM2_P_Z)) (PreH58 : (0 <= 1)) (PreH59 : ((u64_list_value (xs)) = 1)) (PreH60 : (u64_list_bounded xs )) (PreH61 : ((Zlength (xs)) = 4)) (PreH62 : (1 < SM2_P_Z)) (PreH63 : (0 <= 1)) (PreH64 : (P_verifies <> ECInfinity)) (PreH65 : (retval_7 = 0)) (PreH66 : (retval_9 = 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_2 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> SigR_verifies)) (PreH5 : (SigR_verifies < SM2_N_Z)) (PreH6 : (0 <= SigR_verifies)) (PreH7 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH8 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH9 : (retval_10 = 1)) (PreH10 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH11 : (retval_9 = 0)) (PreH12 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH13 : (retval_8 = 1)) (PreH14 : (0 <= retval_7)) (PreH15 : (retval_7 <= 1)) (PreH16 : (retval_7 = 0)) (PreH17 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH18 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH19 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH20 : (retval_6 = 0)) (PreH21 : (0 <= retval_6)) (PreH22 : (retval_6 <= 1)) (PreH23 : (retval_6 = 0)) (PreH24 : (SigS_verifies <> 0)) (PreH25 : (retval_5 = 0)) (PreH26 : (0 <= retval_5)) (PreH27 : (retval_5 <= 1)) (PreH28 : (retval_5 = 0)) (PreH29 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval_4 = 0)) (PreH31 : (0 <= retval_4)) (PreH32 : (retval_4 <= 1)) (PreH33 : (retval_4 = 0)) (PreH34 : (SigR_verifies <> 0)) (PreH35 : (retval_3 = 0)) (PreH36 : (0 <= retval_3)) (PreH37 : (retval_3 <= 1)) (PreH38 : (retval_3 = 0)) (PreH39 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH40 : (retval_2 <> 0)) (PreH41 : (0 <= retval_2)) (PreH42 : (retval_2 <= 1)) (PreH43 : (retval_2 = 1)) (PreH44 : (valid_afpoint x y )) (PreH45 : (valid_afpoint x y )) (PreH46 : (afpoint_represents x y P_verifies )) (PreH47 : ((u64_list_value (zs)) = 0)) (PreH48 : (u64_list_bounded zs )) (PreH49 : ((Zlength (zs)) = 4)) (PreH50 : (0 < SM2_P_Z)) (PreH51 : (0 <= 0)) (PreH52 : ((u64_list_value (ys)) = 1)) (PreH53 : (u64_list_bounded ys )) (PreH54 : ((Zlength (ys)) = 4)) (PreH55 : (1 < SM2_P_Z)) (PreH56 : (0 <= 1)) (PreH57 : ((u64_list_value (xs)) = 1)) (PreH58 : (u64_list_bounded xs )) (PreH59 : ((Zlength (xs)) = 4)) (PreH60 : (1 < SM2_P_Z)) (PreH61 : (0 <= 1)) (PreH62 : (P_verifies <> ECInfinity)) (PreH63 : (retval_7 = 0)) (PreH64 : (retval_9 = 0)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> SigR_verifies)) (PreH7 : (SigR_verifies < SM2_N_Z)) (PreH8 : (0 <= SigR_verifies)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH11 : (retval_10 = 1)) (PreH12 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH13 : (retval_9 = 0)) (PreH14 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH15 : (retval_8 = 1)) (PreH16 : (0 <= retval_7)) (PreH17 : (retval_7 <= 1)) (PreH18 : (retval_7 = 0)) (PreH19 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH20 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH21 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH22 : (retval_6 = 0)) (PreH23 : (0 <= retval_6)) (PreH24 : (retval_6 <= 1)) (PreH25 : (retval_6 = 0)) (PreH26 : (SigS_verifies <> 0)) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= retval_5)) (PreH29 : (retval_5 <= 1)) (PreH30 : (retval_5 = 0)) (PreH31 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval_4 = 0)) (PreH33 : (0 <= retval_4)) (PreH34 : (retval_4 <= 1)) (PreH35 : (retval_4 = 0)) (PreH36 : (SigR_verifies <> 0)) (PreH37 : (retval_3 = 0)) (PreH38 : (0 <= retval_3)) (PreH39 : (retval_3 <= 1)) (PreH40 : (retval_3 = 0)) (PreH41 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH42 : (retval_2 <> 0)) (PreH43 : (0 <= retval_2)) (PreH44 : (retval_2 <= 1)) (PreH45 : (retval_2 = 1)) (PreH46 : (valid_afpoint x y )) (PreH47 : (valid_afpoint x y )) (PreH48 : (afpoint_represents x y P_verifies )) (PreH49 : ((u64_list_value (zs)) = 0)) (PreH50 : (u64_list_bounded zs )) (PreH51 : ((Zlength (zs)) = 4)) (PreH52 : (0 < SM2_P_Z)) (PreH53 : (0 <= 0)) (PreH54 : ((u64_list_value (ys)) = 1)) (PreH55 : (u64_list_bounded ys )) (PreH56 : ((Zlength (ys)) = 4)) (PreH57 : (1 < SM2_P_Z)) (PreH58 : (0 <= 1)) (PreH59 : ((u64_list_value (xs)) = 1)) (PreH60 : (u64_list_bounded xs )) (PreH61 : ((Zlength (xs)) = 4)) (PreH62 : (1 < SM2_P_Z)) (PreH63 : (0 <= 1)) (PreH64 : (P_verifies <> ECInfinity)) (PreH65 : (retval_7 = 0)) (PreH66 : (retval_9 = 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_2_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> SigR_verifies)) (PreH7 : (SigR_verifies < SM2_N_Z)) (PreH8 : (0 <= SigR_verifies)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH11 : (retval_10 = 1)) (PreH12 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH13 : (retval_9 = 0)) (PreH14 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH15 : (retval_8 = 1)) (PreH16 : (0 <= retval_7)) (PreH17 : (retval_7 <= 1)) (PreH18 : (retval_7 = 0)) (PreH19 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH20 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH21 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH22 : (retval_6 = 0)) (PreH23 : (0 <= retval_6)) (PreH24 : (retval_6 <= 1)) (PreH25 : (retval_6 = 0)) (PreH26 : (SigS_verifies <> 0)) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= retval_5)) (PreH29 : (retval_5 <= 1)) (PreH30 : (retval_5 = 0)) (PreH31 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval_4 = 0)) (PreH33 : (0 <= retval_4)) (PreH34 : (retval_4 <= 1)) (PreH35 : (retval_4 = 0)) (PreH36 : (SigR_verifies <> 0)) (PreH37 : (retval_3 = 0)) (PreH38 : (0 <= retval_3)) (PreH39 : (retval_3 <= 1)) (PreH40 : (retval_3 = 0)) (PreH41 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH42 : (retval_2 <> 0)) (PreH43 : (0 <= retval_2)) (PreH44 : (retval_2 <= 1)) (PreH45 : (retval_2 = 1)) (PreH46 : (valid_afpoint x y )) (PreH47 : (valid_afpoint x y )) (PreH48 : (afpoint_represents x y P_verifies )) (PreH49 : ((u64_list_value (zs)) = 0)) (PreH50 : (u64_list_bounded zs )) (PreH51 : ((Zlength (zs)) = 4)) (PreH52 : (0 < SM2_P_Z)) (PreH53 : (0 <= 0)) (PreH54 : ((u64_list_value (ys)) = 1)) (PreH55 : (u64_list_bounded ys )) (PreH56 : ((Zlength (ys)) = 4)) (PreH57 : (1 < SM2_P_Z)) (PreH58 : (0 <= 1)) (PreH59 : ((u64_list_value (xs)) = 1)) (PreH60 : (u64_list_bounded xs )) (PreH61 : ((Zlength (xs)) = 4)) (PreH62 : (1 < SM2_P_Z)) (PreH63 : (0 <= 1)) (PreH64 : (P_verifies <> ECInfinity)) (PreH65 : (retval_7 = 0)) (PreH66 : (retval_9 = 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
.

Definition sm2_verify_dgst_return_wit_2_split_goal_spatial := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (RX: Z) (RY: Z) (retval_10: Z) (retval: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> SigR_verifies)) (PreH7 : (SigR_verifies < SM2_N_Z)) (PreH8 : (0 <= SigR_verifies)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH11 : (retval_10 = 1)) (PreH12 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH13 : (retval_9 = 0)) (PreH14 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH15 : (retval_8 = 1)) (PreH16 : (0 <= retval_7)) (PreH17 : (retval_7 <= 1)) (PreH18 : (retval_7 = 0)) (PreH19 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH20 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH21 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH22 : (retval_6 = 0)) (PreH23 : (0 <= retval_6)) (PreH24 : (retval_6 <= 1)) (PreH25 : (retval_6 = 0)) (PreH26 : (SigS_verifies <> 0)) (PreH27 : (retval_5 = 0)) (PreH28 : (0 <= retval_5)) (PreH29 : (retval_5 <= 1)) (PreH30 : (retval_5 = 0)) (PreH31 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval_4 = 0)) (PreH33 : (0 <= retval_4)) (PreH34 : (retval_4 <= 1)) (PreH35 : (retval_4 = 0)) (PreH36 : (SigR_verifies <> 0)) (PreH37 : (retval_3 = 0)) (PreH38 : (0 <= retval_3)) (PreH39 : (retval_3 <= 1)) (PreH40 : (retval_3 = 0)) (PreH41 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH42 : (retval_2 <> 0)) (PreH43 : (0 <= retval_2)) (PreH44 : (retval_2 <= 1)) (PreH45 : (retval_2 = 1)) (PreH46 : (valid_afpoint x y )) (PreH47 : (valid_afpoint x y )) (PreH48 : (afpoint_represents x y P_verifies )) (PreH49 : ((u64_list_value (zs)) = 0)) (PreH50 : (u64_list_bounded zs )) (PreH51 : ((Zlength (zs)) = 4)) (PreH52 : (0 < SM2_P_Z)) (PreH53 : (0 <= 0)) (PreH54 : ((u64_list_value (ys)) = 1)) (PreH55 : (u64_list_bounded ys )) (PreH56 : ((Zlength (ys)) = 4)) (PreH57 : (1 < SM2_P_Z)) (PreH58 : (0 <= 1)) (PreH59 : ((u64_list_value (xs)) = 1)) (PreH60 : (u64_list_bounded xs )) (PreH61 : ((Zlength (xs)) = 4)) (PreH62 : (1 < SM2_P_Z)) (PreH63 : (0 <= 1)) (PreH64 : (P_verifies <> ECInfinity)) (PreH65 : (retval_7 = 0)) (PreH66 : (retval_9 = 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_3 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 1)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 <> 0)) ,
  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_sm2_rhon )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (SigR_verifies < SM2_N_Z)) (PreH2 : (0 <= SigR_verifies)) (PreH3 : (SigS_verifies < SM2_N_Z)) (PreH4 : (0 <= SigS_verifies)) (PreH5 : (retval_8 = 1)) (PreH6 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH7 : (retval_7 = 1)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (retval_6 = 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH12 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH14 : (retval_5 = 0)) (PreH15 : (0 <= retval_5)) (PreH16 : (retval_5 <= 1)) (PreH17 : (retval_5 = 0)) (PreH18 : (SigS_verifies <> 0)) (PreH19 : (retval_4 = 0)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (retval_4 = 0)) (PreH23 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH24 : (retval_3 = 0)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (SigR_verifies <> 0)) (PreH29 : (retval_2 = 0)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (retval_2 = 0)) (PreH33 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH34 : (retval <> 0)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (retval = 1)) (PreH38 : (valid_afpoint x y )) (PreH39 : (valid_afpoint x y )) (PreH40 : (afpoint_represents x y P_verifies )) (PreH41 : ((u64_list_value (zs)) = 0)) (PreH42 : (u64_list_bounded zs )) (PreH43 : ((Zlength (zs)) = 4)) (PreH44 : (0 < SM2_P_Z)) (PreH45 : (0 <= 0)) (PreH46 : ((u64_list_value (ys)) = 1)) (PreH47 : (u64_list_bounded ys )) (PreH48 : ((Zlength (ys)) = 4)) (PreH49 : (1 < SM2_P_Z)) (PreH50 : (0 <= 1)) (PreH51 : ((u64_list_value (xs)) = 1)) (PreH52 : (u64_list_bounded xs )) (PreH53 : ((Zlength (xs)) = 4)) (PreH54 : (1 < SM2_P_Z)) (PreH55 : (0 <= 1)) (PreH56 : (P_verifies <> ECInfinity)) (PreH57 : (retval_6 = 0)) (PreH58 : (retval_8 <> 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_3_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (SigR_verifies < SM2_N_Z)) (PreH2 : (0 <= SigR_verifies)) (PreH3 : (SigS_verifies < SM2_N_Z)) (PreH4 : (0 <= SigS_verifies)) (PreH5 : (retval_8 = 1)) (PreH6 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH7 : (retval_7 = 1)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (retval_6 = 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH12 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH14 : (retval_5 = 0)) (PreH15 : (0 <= retval_5)) (PreH16 : (retval_5 <= 1)) (PreH17 : (retval_5 = 0)) (PreH18 : (SigS_verifies <> 0)) (PreH19 : (retval_4 = 0)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (retval_4 = 0)) (PreH23 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH24 : (retval_3 = 0)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (SigR_verifies <> 0)) (PreH29 : (retval_2 = 0)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (retval_2 = 0)) (PreH33 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH34 : (retval <> 0)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (retval = 1)) (PreH38 : (valid_afpoint x y )) (PreH39 : (valid_afpoint x y )) (PreH40 : (afpoint_represents x y P_verifies )) (PreH41 : ((u64_list_value (zs)) = 0)) (PreH42 : (u64_list_bounded zs )) (PreH43 : ((Zlength (zs)) = 4)) (PreH44 : (0 < SM2_P_Z)) (PreH45 : (0 <= 0)) (PreH46 : ((u64_list_value (ys)) = 1)) (PreH47 : (u64_list_bounded ys )) (PreH48 : ((Zlength (ys)) = 4)) (PreH49 : (1 < SM2_P_Z)) (PreH50 : (0 <= 1)) (PreH51 : ((u64_list_value (xs)) = 1)) (PreH52 : (u64_list_bounded xs )) (PreH53 : ((Zlength (xs)) = 4)) (PreH54 : (1 < SM2_P_Z)) (PreH55 : (0 <= 1)) (PreH56 : (P_verifies <> ECInfinity)) (PreH57 : (retval_6 = 0)) (PreH58 : (retval_8 <> 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
.

Definition sm2_verify_dgst_return_wit_3_split_goal_spatial := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (SigR_verifies < SM2_N_Z)) (PreH2 : (0 <= SigR_verifies)) (PreH3 : (SigS_verifies < SM2_N_Z)) (PreH4 : (0 <= SigS_verifies)) (PreH5 : (retval_8 = 1)) (PreH6 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) = ECInfinity)) (PreH7 : (retval_7 = 1)) (PreH8 : (0 <= retval_6)) (PreH9 : (retval_6 <= 1)) (PreH10 : (retval_6 = 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH12 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH14 : (retval_5 = 0)) (PreH15 : (0 <= retval_5)) (PreH16 : (retval_5 <= 1)) (PreH17 : (retval_5 = 0)) (PreH18 : (SigS_verifies <> 0)) (PreH19 : (retval_4 = 0)) (PreH20 : (0 <= retval_4)) (PreH21 : (retval_4 <= 1)) (PreH22 : (retval_4 = 0)) (PreH23 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH24 : (retval_3 = 0)) (PreH25 : (0 <= retval_3)) (PreH26 : (retval_3 <= 1)) (PreH27 : (retval_3 = 0)) (PreH28 : (SigR_verifies <> 0)) (PreH29 : (retval_2 = 0)) (PreH30 : (0 <= retval_2)) (PreH31 : (retval_2 <= 1)) (PreH32 : (retval_2 = 0)) (PreH33 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH34 : (retval <> 0)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (retval = 1)) (PreH38 : (valid_afpoint x y )) (PreH39 : (valid_afpoint x y )) (PreH40 : (afpoint_represents x y P_verifies )) (PreH41 : ((u64_list_value (zs)) = 0)) (PreH42 : (u64_list_bounded zs )) (PreH43 : ((Zlength (zs)) = 4)) (PreH44 : (0 < SM2_P_Z)) (PreH45 : (0 <= 0)) (PreH46 : ((u64_list_value (ys)) = 1)) (PreH47 : (u64_list_bounded ys )) (PreH48 : ((Zlength (ys)) = 4)) (PreH49 : (1 < SM2_P_Z)) (PreH50 : (0 <= 1)) (PreH51 : ((u64_list_value (xs)) = 1)) (PreH52 : (u64_list_bounded xs )) (PreH53 : ((Zlength (xs)) = 4)) (PreH54 : (1 < SM2_P_Z)) (PreH55 : (0 <= 1)) (PreH56 : (P_verifies <> ECInfinity)) (PreH57 : (retval_6 = 0)) (PreH58 : (retval_8 <> 0)) ,
  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_mont_base_point_table )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_4 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 1)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 <> 0)) ,
  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (SigR_verifies < SM2_N_Z)) (PreH4 : (0 <= SigR_verifies)) (PreH5 : (0 <= retval_6)) (PreH6 : (retval_6 <= 1)) (PreH7 : (retval_6 = 1)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH9 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= retval_5)) (PreH13 : (retval_5 <= 1)) (PreH14 : (retval_5 = 0)) (PreH15 : (SigS_verifies <> 0)) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 <= 1)) (PreH19 : (retval_4 = 0)) (PreH20 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval_3 = 0)) (PreH22 : (0 <= retval_3)) (PreH23 : (retval_3 <= 1)) (PreH24 : (retval_3 = 0)) (PreH25 : (SigR_verifies <> 0)) (PreH26 : (retval_2 = 0)) (PreH27 : (0 <= retval_2)) (PreH28 : (retval_2 <= 1)) (PreH29 : (retval_2 = 0)) (PreH30 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH31 : (retval <> 0)) (PreH32 : (0 <= retval)) (PreH33 : (retval <= 1)) (PreH34 : (retval = 1)) (PreH35 : (valid_afpoint x y )) (PreH36 : (valid_afpoint x y )) (PreH37 : (afpoint_represents x y P_verifies )) (PreH38 : ((u64_list_value (zs)) = 0)) (PreH39 : (u64_list_bounded zs )) (PreH40 : ((Zlength (zs)) = 4)) (PreH41 : (0 < SM2_P_Z)) (PreH42 : (0 <= 0)) (PreH43 : ((u64_list_value (ys)) = 1)) (PreH44 : (u64_list_bounded ys )) (PreH45 : ((Zlength (ys)) = 4)) (PreH46 : (1 < SM2_P_Z)) (PreH47 : (0 <= 1)) (PreH48 : ((u64_list_value (xs)) = 1)) (PreH49 : (u64_list_bounded xs )) (PreH50 : ((Zlength (xs)) = 4)) (PreH51 : (1 < SM2_P_Z)) (PreH52 : (0 <= 1)) (PreH53 : (P_verifies <> ECInfinity)) (PreH54 : (retval_6 <> 0)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_4_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (SigR_verifies < SM2_N_Z)) (PreH4 : (0 <= SigR_verifies)) (PreH5 : (0 <= retval_6)) (PreH6 : (retval_6 <= 1)) (PreH7 : (retval_6 = 1)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH9 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= retval_5)) (PreH13 : (retval_5 <= 1)) (PreH14 : (retval_5 = 0)) (PreH15 : (SigS_verifies <> 0)) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 <= 1)) (PreH19 : (retval_4 = 0)) (PreH20 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval_3 = 0)) (PreH22 : (0 <= retval_3)) (PreH23 : (retval_3 <= 1)) (PreH24 : (retval_3 = 0)) (PreH25 : (SigR_verifies <> 0)) (PreH26 : (retval_2 = 0)) (PreH27 : (0 <= retval_2)) (PreH28 : (retval_2 <= 1)) (PreH29 : (retval_2 = 0)) (PreH30 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH31 : (retval <> 0)) (PreH32 : (0 <= retval)) (PreH33 : (retval <= 1)) (PreH34 : (retval = 1)) (PreH35 : (valid_afpoint x y )) (PreH36 : (valid_afpoint x y )) (PreH37 : (afpoint_represents x y P_verifies )) (PreH38 : ((u64_list_value (zs)) = 0)) (PreH39 : (u64_list_bounded zs )) (PreH40 : ((Zlength (zs)) = 4)) (PreH41 : (0 < SM2_P_Z)) (PreH42 : (0 <= 0)) (PreH43 : ((u64_list_value (ys)) = 1)) (PreH44 : (u64_list_bounded ys )) (PreH45 : ((Zlength (ys)) = 4)) (PreH46 : (1 < SM2_P_Z)) (PreH47 : (0 <= 1)) (PreH48 : ((u64_list_value (xs)) = 1)) (PreH49 : (u64_list_bounded xs )) (PreH50 : ((Zlength (xs)) = 4)) (PreH51 : (1 < SM2_P_Z)) (PreH52 : (0 <= 1)) (PreH53 : (P_verifies <> ECInfinity)) (PreH54 : (retval_6 <> 0)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
.

Definition sm2_verify_dgst_return_wit_4_split_goal_spatial := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (SigS_verifies < SM2_N_Z)) (PreH2 : (0 <= SigS_verifies)) (PreH3 : (SigR_verifies < SM2_N_Z)) (PreH4 : (0 <= SigR_verifies)) (PreH5 : (0 <= retval_6)) (PreH6 : (retval_6 <= 1)) (PreH7 : (retval_6 = 1)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) = 0)) (PreH9 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH10 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH11 : (retval_5 = 0)) (PreH12 : (0 <= retval_5)) (PreH13 : (retval_5 <= 1)) (PreH14 : (retval_5 = 0)) (PreH15 : (SigS_verifies <> 0)) (PreH16 : (retval_4 = 0)) (PreH17 : (0 <= retval_4)) (PreH18 : (retval_4 <= 1)) (PreH19 : (retval_4 = 0)) (PreH20 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval_3 = 0)) (PreH22 : (0 <= retval_3)) (PreH23 : (retval_3 <= 1)) (PreH24 : (retval_3 = 0)) (PreH25 : (SigR_verifies <> 0)) (PreH26 : (retval_2 = 0)) (PreH27 : (0 <= retval_2)) (PreH28 : (retval_2 <= 1)) (PreH29 : (retval_2 = 0)) (PreH30 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH31 : (retval <> 0)) (PreH32 : (0 <= retval)) (PreH33 : (retval <= 1)) (PreH34 : (retval = 1)) (PreH35 : (valid_afpoint x y )) (PreH36 : (valid_afpoint x y )) (PreH37 : (afpoint_represents x y P_verifies )) (PreH38 : ((u64_list_value (zs)) = 0)) (PreH39 : (u64_list_bounded zs )) (PreH40 : ((Zlength (zs)) = 4)) (PreH41 : (0 < SM2_P_Z)) (PreH42 : (0 <= 0)) (PreH43 : ((u64_list_value (ys)) = 1)) (PreH44 : (u64_list_bounded ys )) (PreH45 : ((Zlength (ys)) = 4)) (PreH46 : (1 < SM2_P_Z)) (PreH47 : (0 <= 1)) (PreH48 : ((u64_list_value (xs)) = 1)) (PreH49 : (u64_list_bounded xs )) (PreH50 : ((Zlength (xs)) = 4)) (PreH51 : (1 < SM2_P_Z)) (PreH52 : (0 <= 1)) (PreH53 : (P_verifies <> ECInfinity)) (PreH54 : (retval_6 <> 0)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_5 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_5_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
.

Definition sm2_verify_dgst_return_wit_5_split_goal_2 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition sm2_verify_dgst_return_wit_5_split_goal_spatial := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_6 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_6_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
.

Definition sm2_verify_dgst_return_wit_6_split_goal_2 := 
forall (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition sm2_verify_dgst_return_wit_6_split_goal_spatial := 
forall (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_7 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies 0 SigS_verifies )) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_7_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies 0 SigS_verifies )) ”
.

Definition sm2_verify_dgst_return_wit_7_split_goal_2 := 
forall (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition sm2_verify_dgst_return_wit_7_split_goal_spatial := 
forall (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_return_wit_8 := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
) \/
(
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies 0 )) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
).

Definition sm2_verify_dgst_return_wit_8_split_goal_1 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies 0 )) ”
.

Definition sm2_verify_dgst_return_wit_8_split_goal_2 := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition sm2_verify_dgst_return_wit_8_split_goal_spatial := 
forall (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : (SigS_verifies = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
.

Definition sm2_verify_dgst_partial_solve_wit_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (P_verifies <> ECInfinity)) ,
  (UndefStructPredJPoint ( &( "tmp1" ) ) )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (UInt64Array.undef_full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.undef_full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = 0)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (0 < SM2_P_Z)) (PreH5 : (0 <= 0)) (PreH6 : ((u64_list_value (ys)) = 1)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (1 < SM2_P_Z)) (PreH10 : (0 <= 1)) (PreH11 : ((u64_list_value (xs)) = 1)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (1 < SM2_P_Z)) (PreH15 : (0 <= 1)) (PreH16 : (P_verifies <> ECInfinity)) ,
  (UndefStructPredJPoint ( &( "point1_jacobian" ) ) )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (UInt64Array.undef_full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.undef_full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_3 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (PreH1 : (valid_afpoint x y )) (PreH2 : (afpoint_represents x y P_verifies )) (PreH3 : ((u64_list_value (zs)) = 0)) (PreH4 : (u64_list_bounded zs )) (PreH5 : ((Zlength (zs)) = 4)) (PreH6 : (0 < SM2_P_Z)) (PreH7 : (0 <= 0)) (PreH8 : ((u64_list_value (ys)) = 1)) (PreH9 : (u64_list_bounded ys )) (PreH10 : ((Zlength (ys)) = 4)) (PreH11 : (1 < SM2_P_Z)) (PreH12 : (0 <= 1)) (PreH13 : ((u64_list_value (xs)) = 1)) (PreH14 : (u64_list_bounded xs )) (PreH15 : ((Zlength (xs)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : (P_verifies <> ECInfinity)) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_4 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_verifies )) (PreH8 : ((u64_list_value (zs)) = 0)) (PreH9 : (u64_list_bounded zs )) (PreH10 : ((Zlength (zs)) = 4)) (PreH11 : (0 < SM2_P_Z)) (PreH12 : (0 <= 0)) (PreH13 : ((u64_list_value (ys)) = 1)) (PreH14 : (u64_list_bounded ys )) (PreH15 : ((Zlength (ys)) = 4)) (PreH16 : (1 < SM2_P_Z)) (PreH17 : (0 <= 1)) (PreH18 : ((u64_list_value (xs)) = 1)) (PreH19 : (u64_list_bounded xs )) (PreH20 : ((Zlength (xs)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : (P_verifies <> ECInfinity)) ,
  (UInt64Array.full &(( &( "SM2_N" ) )->ₛ "v") 4 (cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))) )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_5 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_6 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_verifies )) (PreH13 : ((u64_list_value (zs)) = 0)) (PreH14 : (u64_list_bounded zs )) (PreH15 : ((Zlength (zs)) = 4)) (PreH16 : (0 < SM2_P_Z)) (PreH17 : (0 <= 0)) (PreH18 : ((u64_list_value (ys)) = 1)) (PreH19 : (u64_list_bounded ys )) (PreH20 : ((Zlength (ys)) = 4)) (PreH21 : (1 < SM2_P_Z)) (PreH22 : (0 <= 1)) (PreH23 : ((u64_list_value (xs)) = 1)) (PreH24 : (u64_list_bounded xs )) (PreH25 : ((Zlength (xs)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (SigR_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_7 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (SigR_verifies = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (SigR_verifies = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_8 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 0)) (PreH5 : (SigR_verifies <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (valid_afpoint x y )) (PreH16 : (valid_afpoint x y )) (PreH17 : (afpoint_represents x y P_verifies )) (PreH18 : ((u64_list_value (zs)) = 0)) (PreH19 : (u64_list_bounded zs )) (PreH20 : ((Zlength (zs)) = 4)) (PreH21 : (0 < SM2_P_Z)) (PreH22 : (0 <= 0)) (PreH23 : ((u64_list_value (ys)) = 1)) (PreH24 : (u64_list_bounded ys )) (PreH25 : ((Zlength (ys)) = 4)) (PreH26 : (1 < SM2_P_Z)) (PreH27 : (0 <= 1)) (PreH28 : ((u64_list_value (xs)) = 1)) (PreH29 : (u64_list_bounded xs )) (PreH30 : ((Zlength (xs)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_9 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (SigS_verifies >= (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_10 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 0)) (PreH5 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH6 : (retval_3 = 0)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (SigR_verifies <> 0)) (PreH11 : (retval_2 = 0)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH16 : (retval <> 0)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (valid_afpoint x y )) (PreH21 : (valid_afpoint x y )) (PreH22 : (afpoint_represents x y P_verifies )) (PreH23 : ((u64_list_value (zs)) = 0)) (PreH24 : (u64_list_bounded zs )) (PreH25 : ((Zlength (zs)) = 4)) (PreH26 : (0 < SM2_P_Z)) (PreH27 : (0 <= 0)) (PreH28 : ((u64_list_value (ys)) = 1)) (PreH29 : (u64_list_bounded ys )) (PreH30 : ((Zlength (ys)) = 4)) (PreH31 : (1 < SM2_P_Z)) (PreH32 : (0 <= 1)) (PreH33 : ((u64_list_value (xs)) = 1)) (PreH34 : (u64_list_bounded xs )) (PreH35 : ((Zlength (xs)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_11_pure := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= SigR_verifies) ” 
  &&  “ (SigR_verifies < SM2_N_Z) ” 
  &&  “ (0 <= SigS_verifies) ” 
  &&  “ (SigS_verifies < SM2_N_Z) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
) \/
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ” 
  &&  “ (SigS_verifies < SM2_N_Z) ” 
  &&  “ (0 <= SigS_verifies) ” 
  &&  “ (SigR_verifies < SM2_N_Z) ” 
  &&  “ (0 <= SigR_verifies) ”
).

Definition sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ”
.

Definition sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_2 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (SigS_verifies < SM2_N_Z) ”
.

Definition sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_3 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= SigS_verifies) ”
.

Definition sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_4 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (SigR_verifies < SM2_N_Z) ”
.

Definition sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_5 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= SigR_verifies) ”
.

Definition sm2_verify_dgst_partial_solve_wit_11_aux := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_u256 ( &( "SM2_N" ) ) (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= SigR_verifies) ” 
  &&  “ (SigR_verifies < SM2_N_Z) ” 
  &&  “ (0 <= SigS_verifies) ” 
  &&  “ (SigS_verifies < SM2_N_Z) ” 
  &&  “ ((u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))) = SM2_N_Z) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (UInt64Array.undef_full &(( &( "t" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_11 := sm2_verify_dgst_partial_solve_wit_11_pure -> sm2_verify_dgst_partial_solve_wit_11_aux.

Definition sm2_verify_dgst_partial_solve_wit_12 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : (SigS_verifies <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH11 : (retval_3 = 0)) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : (SigR_verifies <> 0)) (PreH16 : (retval_2 = 0)) (PreH17 : (0 <= retval_2)) (PreH18 : (retval_2 <= 1)) (PreH19 : (retval_2 = 0)) (PreH20 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH21 : (retval <> 0)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (valid_afpoint x y )) (PreH26 : (valid_afpoint x y )) (PreH27 : (afpoint_represents x y P_verifies )) (PreH28 : ((u64_list_value (zs)) = 0)) (PreH29 : (u64_list_bounded zs )) (PreH30 : ((Zlength (zs)) = 4)) (PreH31 : (0 < SM2_P_Z)) (PreH32 : (0 <= 0)) (PreH33 : ((u64_list_value (ys)) = 1)) (PreH34 : (u64_list_bounded ys )) (PreH35 : ((Zlength (ys)) = 4)) (PreH36 : (1 < SM2_P_Z)) (PreH37 : (0 <= 1)) (PreH38 : ((u64_list_value (xs)) = 1)) (PreH39 : (u64_list_bounded xs )) (PreH40 : ((Zlength (xs)) = 4)) (PreH41 : (1 < SM2_P_Z)) (PreH42 : (0 <= 1)) (PreH43 : (P_verifies <> ECInfinity)) ,
  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ”
  &&  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
.

Definition sm2_verify_dgst_partial_solve_wit_13 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
|--
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_partial_solve_wit_14 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
|--
  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (UInt64Array.undef_full &(( &( "tmp1" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp1" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp1" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_partial_solve_wit_15_pure := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (P_verifies <> ECInfinity) ”
.

Definition sm2_verify_dgst_partial_solve_wit_15_aux := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_u256 ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
|--
  “ (P_verifies <> ECInfinity) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "point1_jacobian" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "point1_jacobian" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "point1_jacobian" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_partial_solve_wit_15 := sm2_verify_dgst_partial_solve_wit_15_pure -> sm2_verify_dgst_partial_solve_wit_15_aux.

Definition sm2_verify_dgst_partial_solve_wit_16_pure := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (( &( "point1_jacobian" ) ) = ( &( "point1_jacobian" ) )) ”
.

Definition sm2_verify_dgst_partial_solve_wit_16_aux := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= 1)) (PreH3 : (retval_6 = 0)) (PreH4 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH5 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH6 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH7 : (retval_5 = 0)) (PreH8 : (0 <= retval_5)) (PreH9 : (retval_5 <= 1)) (PreH10 : (retval_5 = 0)) (PreH11 : (SigS_verifies <> 0)) (PreH12 : (retval_4 = 0)) (PreH13 : (0 <= retval_4)) (PreH14 : (retval_4 <= 1)) (PreH15 : (retval_4 = 0)) (PreH16 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH17 : (retval_3 = 0)) (PreH18 : (0 <= retval_3)) (PreH19 : (retval_3 <= 1)) (PreH20 : (retval_3 = 0)) (PreH21 : (SigR_verifies <> 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH27 : (retval <> 0)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (valid_afpoint x y )) (PreH32 : (valid_afpoint x y )) (PreH33 : (afpoint_represents x y P_verifies )) (PreH34 : ((u64_list_value (zs)) = 0)) (PreH35 : (u64_list_bounded zs )) (PreH36 : ((Zlength (zs)) = 4)) (PreH37 : (0 < SM2_P_Z)) (PreH38 : (0 <= 0)) (PreH39 : ((u64_list_value (ys)) = 1)) (PreH40 : (u64_list_bounded ys )) (PreH41 : ((Zlength (ys)) = 4)) (PreH42 : (1 < SM2_P_Z)) (PreH43 : (0 <= 1)) (PreH44 : ((u64_list_value (xs)) = 1)) (PreH45 : (u64_list_bounded xs )) (PreH46 : ((Zlength (xs)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : (P_verifies <> ECInfinity)) (PreH50 : (retval_6 = 0)) ,
  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  “ (( &( "point1_jacobian" ) ) = ( &( "point1_jacobian" ) )) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_partial_solve_wit_16 := sm2_verify_dgst_partial_solve_wit_16_pure -> sm2_verify_dgst_partial_solve_wit_16_aux.

Definition sm2_verify_dgst_partial_solve_wit_17 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = 1)) (PreH2 : (( &( "point1_jacobian" ) ) = ( &( "point1_jacobian" ) ))) (PreH3 : (0 <= retval_6)) (PreH4 : (retval_6 <= 1)) (PreH5 : (retval_6 = 0)) (PreH6 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH8 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH9 : (retval_5 = 0)) (PreH10 : (0 <= retval_5)) (PreH11 : (retval_5 <= 1)) (PreH12 : (retval_5 = 0)) (PreH13 : (SigS_verifies <> 0)) (PreH14 : (retval_4 = 0)) (PreH15 : (0 <= retval_4)) (PreH16 : (retval_4 <= 1)) (PreH17 : (retval_4 = 0)) (PreH18 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH19 : (retval_3 = 0)) (PreH20 : (0 <= retval_3)) (PreH21 : (retval_3 <= 1)) (PreH22 : (retval_3 = 0)) (PreH23 : (SigR_verifies <> 0)) (PreH24 : (retval_2 = 0)) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH29 : (retval <> 0)) (PreH30 : (0 <= retval)) (PreH31 : (retval <= 1)) (PreH32 : (retval = 1)) (PreH33 : (valid_afpoint x y )) (PreH34 : (valid_afpoint x y )) (PreH35 : (afpoint_represents x y P_verifies )) (PreH36 : ((u64_list_value (zs)) = 0)) (PreH37 : (u64_list_bounded zs )) (PreH38 : ((Zlength (zs)) = 4)) (PreH39 : (0 < SM2_P_Z)) (PreH40 : (0 <= 0)) (PreH41 : ((u64_list_value (ys)) = 1)) (PreH42 : (u64_list_bounded ys )) (PreH43 : ((Zlength (ys)) = 4)) (PreH44 : (1 < SM2_P_Z)) (PreH45 : (0 <= 1)) (PreH46 : ((u64_list_value (xs)) = 1)) (PreH47 : (u64_list_bounded xs )) (PreH48 : ((Zlength (xs)) = 4)) (PreH49 : (1 < SM2_P_Z)) (PreH50 : (0 <= 1)) (PreH51 : (P_verifies <> ECInfinity)) (PreH52 : (retval_6 = 0)) ,
  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ”
  &&  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_partial_solve_wit_18_pure := 
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (0 = 0) ” 
  &&  “ ((&(( &( "t" ) )->ₛ "v") + (0 * sizeof(UINT64))) <> 0) ”
) \/
(
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ ((&(( &( "t" ) )->ₛ "v") + (0 * sizeof(UINT64))) <> 0) ”
).

Definition sm2_verify_dgst_partial_solve_wit_18_pure_split_goal_1 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ ((&(( &( "t" ) )->ₛ "v") + (0 * sizeof(UINT64))) <> 0) ”
.

Definition sm2_verify_dgst_partial_solve_wit_18_aux := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = 0)) (PreH2 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH3 : (retval_7 = 1)) (PreH4 : (0 <= retval_6)) (PreH5 : (retval_6 <= 1)) (PreH6 : (retval_6 = 0)) (PreH7 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH8 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH10 : (retval_5 = 0)) (PreH11 : (0 <= retval_5)) (PreH12 : (retval_5 <= 1)) (PreH13 : (retval_5 = 0)) (PreH14 : (SigS_verifies <> 0)) (PreH15 : (retval_4 = 0)) (PreH16 : (0 <= retval_4)) (PreH17 : (retval_4 <= 1)) (PreH18 : (retval_4 = 0)) (PreH19 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH20 : (retval_3 = 0)) (PreH21 : (0 <= retval_3)) (PreH22 : (retval_3 <= 1)) (PreH23 : (retval_3 = 0)) (PreH24 : (SigR_verifies <> 0)) (PreH25 : (retval_2 = 0)) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH30 : (retval <> 0)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (valid_afpoint x y )) (PreH35 : (valid_afpoint x y )) (PreH36 : (afpoint_represents x y P_verifies )) (PreH37 : ((u64_list_value (zs)) = 0)) (PreH38 : (u64_list_bounded zs )) (PreH39 : ((Zlength (zs)) = 4)) (PreH40 : (0 < SM2_P_Z)) (PreH41 : (0 <= 0)) (PreH42 : ((u64_list_value (ys)) = 1)) (PreH43 : (u64_list_bounded ys )) (PreH44 : ((Zlength (ys)) = 4)) (PreH45 : (1 < SM2_P_Z)) (PreH46 : (0 <= 1)) (PreH47 : ((u64_list_value (xs)) = 1)) (PreH48 : (u64_list_bounded xs )) (PreH49 : ((Zlength (xs)) = 4)) (PreH50 : (1 < SM2_P_Z)) (PreH51 : (0 <= 1)) (PreH52 : (P_verifies <> ECInfinity)) (PreH53 : (retval_6 = 0)) (PreH54 : (retval_8 = 0)) ,
  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_fn ( &( "t" ) ) (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) )
  **  (store_sm2_h )
  **  (store_montg_one )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  “ (0 = 0) ” 
  &&  “ ((&(( &( "t" ) )->ₛ "v") + (0 * sizeof(UINT64))) <> 0) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (UInt64Array.undef_full (&(( &( "t" ) )->ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
.

Definition sm2_verify_dgst_partial_solve_wit_18 := sm2_verify_dgst_partial_solve_wit_18_pure -> sm2_verify_dgst_partial_solve_wit_18_aux.

Definition sm2_verify_dgst_partial_solve_wit_19_pure := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : (0 = 0)) (PreH3 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH4 : (retval_8 = 0)) (PreH5 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH6 : (retval_7 = 1)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH13 : (retval_5 = 0)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (SigS_verifies <> 0)) (PreH18 : (retval_4 = 0)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (retval_4 = 0)) (PreH22 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH23 : (retval_3 = 0)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (retval_3 = 0)) (PreH27 : (SigR_verifies <> 0)) (PreH28 : (retval_2 = 0)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH33 : (retval <> 0)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (retval = 1)) (PreH37 : (valid_afpoint x y )) (PreH38 : (valid_afpoint x y )) (PreH39 : (afpoint_represents x y P_verifies )) (PreH40 : ((u64_list_value (zs)) = 0)) (PreH41 : (u64_list_bounded zs )) (PreH42 : ((Zlength (zs)) = 4)) (PreH43 : (0 < SM2_P_Z)) (PreH44 : (0 <= 0)) (PreH45 : ((u64_list_value (ys)) = 1)) (PreH46 : (u64_list_bounded ys )) (PreH47 : ((Zlength (ys)) = 4)) (PreH48 : (1 < SM2_P_Z)) (PreH49 : (0 <= 1)) (PreH50 : ((u64_list_value (xs)) = 1)) (PreH51 : (u64_list_bounded xs )) (PreH52 : ((Zlength (xs)) = 4)) (PreH53 : (1 < SM2_P_Z)) (PreH54 : (0 <= 1)) (PreH55 : (P_verifies <> ECInfinity)) (PreH56 : (retval_6 = 0)) (PreH57 : (retval_8 = 0)) ,
  (store_u256 ( &( "t" ) ) RX )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (( &( "e" ) ) = ( &( "e" ) )) ”
.

Definition sm2_verify_dgst_partial_solve_wit_19_aux := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : (0 = 0)) (PreH3 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH4 : (retval_8 = 0)) (PreH5 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH6 : (retval_7 = 1)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH13 : (retval_5 = 0)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (SigS_verifies <> 0)) (PreH18 : (retval_4 = 0)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (retval_4 = 0)) (PreH22 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH23 : (retval_3 = 0)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (retval_3 = 0)) (PreH27 : (SigR_verifies <> 0)) (PreH28 : (retval_2 = 0)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH33 : (retval <> 0)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (retval = 1)) (PreH37 : (valid_afpoint x y )) (PreH38 : (valid_afpoint x y )) (PreH39 : (afpoint_represents x y P_verifies )) (PreH40 : ((u64_list_value (zs)) = 0)) (PreH41 : (u64_list_bounded zs )) (PreH42 : ((Zlength (zs)) = 4)) (PreH43 : (0 < SM2_P_Z)) (PreH44 : (0 <= 0)) (PreH45 : ((u64_list_value (ys)) = 1)) (PreH46 : (u64_list_bounded ys )) (PreH47 : ((Zlength (ys)) = 4)) (PreH48 : (1 < SM2_P_Z)) (PreH49 : (0 <= 1)) (PreH50 : ((u64_list_value (xs)) = 1)) (PreH51 : (u64_list_bounded xs )) (PreH52 : ((Zlength (xs)) = 4)) (PreH53 : (1 < SM2_P_Z)) (PreH54 : (0 <= 1)) (PreH55 : (P_verifies <> ECInfinity)) (PreH56 : (retval_6 = 0)) (PreH57 : (retval_8 = 0)) ,
  (store_u256 ( &( "t" ) ) RX )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_n )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  (store_sm2_rhon )
|--
  “ (( &( "e" ) ) = ( &( "e" ) )) ” 
  &&  “ (retval_9 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) ) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes_verifies)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "t" ) ) RX )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
.

Definition sm2_verify_dgst_partial_solve_wit_19 := sm2_verify_dgst_partial_solve_wit_19_pure -> sm2_verify_dgst_partial_solve_wit_19_aux.

Definition sm2_verify_dgst_partial_solve_wit_20_pure := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (( &( "e" ) ) = ( &( "e" ) ))) (PreH2 : (retval_9 = 1)) (PreH3 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH4 : (retval_8 = 0)) (PreH5 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH6 : (retval_7 = 1)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH13 : (retval_5 = 0)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (SigS_verifies <> 0)) (PreH18 : (retval_4 = 0)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (retval_4 = 0)) (PreH22 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH23 : (retval_3 = 0)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (retval_3 = 0)) (PreH27 : (SigR_verifies <> 0)) (PreH28 : (retval_2 = 0)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH33 : (retval <> 0)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (retval = 1)) (PreH37 : (valid_afpoint x y )) (PreH38 : (valid_afpoint x y )) (PreH39 : (afpoint_represents x y P_verifies )) (PreH40 : ((u64_list_value (zs)) = 0)) (PreH41 : (u64_list_bounded zs )) (PreH42 : ((Zlength (zs)) = 4)) (PreH43 : (0 < SM2_P_Z)) (PreH44 : (0 <= 0)) (PreH45 : ((u64_list_value (ys)) = 1)) (PreH46 : (u64_list_bounded ys )) (PreH47 : ((Zlength (ys)) = 4)) (PreH48 : (1 < SM2_P_Z)) (PreH49 : (0 <= 1)) (PreH50 : ((u64_list_value (xs)) = 1)) (PreH51 : (u64_list_bounded xs )) (PreH52 : ((Zlength (xs)) = 4)) (PreH53 : (1 < SM2_P_Z)) (PreH54 : (0 <= 1)) (PreH55 : (P_verifies <> ECInfinity)) (PreH56 : (retval_6 = 0)) (PreH57 : (retval_8 = 0)) ,
  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "t" ) ) RX )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  ((( &( "s" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "s"))
  **  ((( &( "r" ) )) # Ptr  |-> &((signature_pre)  # "SM2SIG" ->ₛ "r"))
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
  **  ((( &( "signature" ) )) # Ptr  |-> signature_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (( &( "t" ) ) = ( &( "t" ) )) ”
.

Definition sm2_verify_dgst_partial_solve_wit_20_aux := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (( &( "e" ) ) = ( &( "e" ) ))) (PreH2 : (retval_9 = 1)) (PreH3 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH4 : (retval_8 = 0)) (PreH5 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH6 : (retval_7 = 1)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH13 : (retval_5 = 0)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (SigS_verifies <> 0)) (PreH18 : (retval_4 = 0)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (retval_4 = 0)) (PreH22 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH23 : (retval_3 = 0)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (retval_3 = 0)) (PreH27 : (SigR_verifies <> 0)) (PreH28 : (retval_2 = 0)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH33 : (retval <> 0)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (retval = 1)) (PreH37 : (valid_afpoint x y )) (PreH38 : (valid_afpoint x y )) (PreH39 : (afpoint_represents x y P_verifies )) (PreH40 : ((u64_list_value (zs)) = 0)) (PreH41 : (u64_list_bounded zs )) (PreH42 : ((Zlength (zs)) = 4)) (PreH43 : (0 < SM2_P_Z)) (PreH44 : (0 <= 0)) (PreH45 : ((u64_list_value (ys)) = 1)) (PreH46 : (u64_list_bounded ys )) (PreH47 : ((Zlength (ys)) = 4)) (PreH48 : (1 < SM2_P_Z)) (PreH49 : (0 <= 1)) (PreH50 : ((u64_list_value (xs)) = 1)) (PreH51 : (u64_list_bounded xs )) (PreH52 : ((Zlength (xs)) = 4)) (PreH53 : (1 < SM2_P_Z)) (PreH54 : (0 <= 1)) (PreH55 : (P_verifies <> ECInfinity)) (PreH56 : (retval_6 = 0)) (PreH57 : (retval_8 = 0)) ,
  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "t" ) ) RX )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
|--
  “ (( &( "t" ) ) = ( &( "t" ) )) ” 
  &&  “ (retval_9 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) ) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 ( &( "t" ) ) RX )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
.

Definition sm2_verify_dgst_partial_solve_wit_20 := sm2_verify_dgst_partial_solve_wit_20_pure -> sm2_verify_dgst_partial_solve_wit_20_aux.

Definition sm2_verify_dgst_partial_solve_wit_21 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (( &( "t" ) ) = ( &( "t" ) ))) (PreH2 : (retval_9 = 1)) (PreH3 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH4 : (retval_8 = 0)) (PreH5 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH6 : (retval_7 = 1)) (PreH7 : (0 <= retval_6)) (PreH8 : (retval_6 <= 1)) (PreH9 : (retval_6 = 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH13 : (retval_5 = 0)) (PreH14 : (0 <= retval_5)) (PreH15 : (retval_5 <= 1)) (PreH16 : (retval_5 = 0)) (PreH17 : (SigS_verifies <> 0)) (PreH18 : (retval_4 = 0)) (PreH19 : (0 <= retval_4)) (PreH20 : (retval_4 <= 1)) (PreH21 : (retval_4 = 0)) (PreH22 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH23 : (retval_3 = 0)) (PreH24 : (0 <= retval_3)) (PreH25 : (retval_3 <= 1)) (PreH26 : (retval_3 = 0)) (PreH27 : (SigR_verifies <> 0)) (PreH28 : (retval_2 = 0)) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH33 : (retval <> 0)) (PreH34 : (0 <= retval)) (PreH35 : (retval <= 1)) (PreH36 : (retval = 1)) (PreH37 : (valid_afpoint x y )) (PreH38 : (valid_afpoint x y )) (PreH39 : (afpoint_represents x y P_verifies )) (PreH40 : ((u64_list_value (zs)) = 0)) (PreH41 : (u64_list_bounded zs )) (PreH42 : ((Zlength (zs)) = 4)) (PreH43 : (0 < SM2_P_Z)) (PreH44 : (0 <= 0)) (PreH45 : ((u64_list_value (ys)) = 1)) (PreH46 : (u64_list_bounded ys )) (PreH47 : ((Zlength (ys)) = 4)) (PreH48 : (1 < SM2_P_Z)) (PreH49 : (0 <= 1)) (PreH50 : ((u64_list_value (xs)) = 1)) (PreH51 : (u64_list_bounded xs )) (PreH52 : ((Zlength (xs)) = 4)) (PreH53 : (1 < SM2_P_Z)) (PreH54 : (0 <= 1)) (PreH55 : (P_verifies <> ECInfinity)) (PreH56 : (retval_6 = 0)) (PreH57 : (retval_8 = 0)) ,
  (store_fn ( &( "t" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "R" ) ) )
|--
  “ (retval_9 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) ) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_fn ( &( "t" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "R" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
.

Definition sm2_verify_dgst_partial_solve_wit_22 := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (DigestBytes_verifies: (@list Z)) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (RX: Z) (RY: Z) (retval_9: Z) (PreH1 : (retval_9 = 1)) (PreH2 : (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )) (PreH3 : (retval_8 = 0)) (PreH4 : ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity)) (PreH5 : (retval_7 = 1)) (PreH6 : (0 <= retval_6)) (PreH7 : (retval_6 <= 1)) (PreH8 : (retval_6 = 0)) (PreH9 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0)) (PreH10 : ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z)) (PreH11 : (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)))) (PreH12 : (retval_5 = 0)) (PreH13 : (0 <= retval_5)) (PreH14 : (retval_5 <= 1)) (PreH15 : (retval_5 = 0)) (PreH16 : (SigS_verifies <> 0)) (PreH17 : (retval_4 = 0)) (PreH18 : (0 <= retval_4)) (PreH19 : (retval_4 <= 1)) (PreH20 : (retval_4 = 0)) (PreH21 : (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH22 : (retval_3 = 0)) (PreH23 : (0 <= retval_3)) (PreH24 : (retval_3 <= 1)) (PreH25 : (retval_3 = 0)) (PreH26 : (SigR_verifies <> 0)) (PreH27 : (retval_2 = 0)) (PreH28 : (0 <= retval_2)) (PreH29 : (retval_2 <= 1)) (PreH30 : (retval_2 = 0)) (PreH31 : (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z))))))))))))) (PreH32 : (retval <> 0)) (PreH33 : (0 <= retval)) (PreH34 : (retval <= 1)) (PreH35 : (retval = 1)) (PreH36 : (valid_afpoint x y )) (PreH37 : (valid_afpoint x y )) (PreH38 : (afpoint_represents x y P_verifies )) (PreH39 : ((u64_list_value (zs)) = 0)) (PreH40 : (u64_list_bounded zs )) (PreH41 : ((Zlength (zs)) = 4)) (PreH42 : (0 < SM2_P_Z)) (PreH43 : (0 <= 0)) (PreH44 : ((u64_list_value (ys)) = 1)) (PreH45 : (u64_list_bounded ys )) (PreH46 : ((Zlength (ys)) = 4)) (PreH47 : (1 < SM2_P_Z)) (PreH48 : (0 <= 1)) (PreH49 : ((u64_list_value (xs)) = 1)) (PreH50 : (u64_list_bounded xs )) (PreH51 : ((Zlength (xs)) = 4)) (PreH52 : (1 < SM2_P_Z)) (PreH53 : (0 <= 1)) (PreH54 : (P_verifies <> ECInfinity)) (PreH55 : (retval_6 = 0)) (PreH56 : (retval_8 = 0)) ,
  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_fn ( &( "t" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (store_fn ( &( "R" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
|--
  “ (SigR_verifies < SM2_N_Z) ” 
  &&  “ (0 <= SigR_verifies) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_9 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) ) ” 
  &&  “ (retval_8 = 0) ” 
  &&  “ ((sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) <> ECInfinity) ” 
  &&  “ (retval_7 = 1) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (SigS_verifies <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (SigS_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (SigR_verifies <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (SigR_verifies < (u64_list_value ((cons (SM2_N0_Z) ((cons (SM2_N1_Z) ((cons (SM2_N2_Z) ((cons (SM2_N3_Z) ((@nil Z)))))))))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_verifies ) ” 
  &&  “ ((u64_list_value (zs)) = 0) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((u64_list_value (ys)) = 1) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((u64_list_value (xs)) = 1) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (1 < SM2_P_Z) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (retval_8 = 0) ”
  &&  (store_u256 ( &( "R" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 &((signature_pre)  # "SM2SIG" ->ₛ "r") SigR_verifies )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes_verifies))) (SM2_N_Z)) )
  **  (store_fn ( &( "t" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "point1_jacobian" ) ) (sm2_point_add ((sm2_point_mul (SigS_verifies) (SM2_G_POINT))) ((sm2_point_mul ((Zmod ((SigR_verifies + SigS_verifies )) (SM2_N_Z))) (P_verifies)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_jpoint ( &( "tmp1" ) ) (sm2_point_mul (SigS_verifies) (SM2_G_POINT)) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_h )
  **  (store_fn &((signature_pre)  # "SM2SIG" ->ₛ "s") SigS_verifies )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &(( &( "JPoint_ZERO" ) )->ₛ "x" .ₛ "v") 4 xs )
.

Definition sm2_verify_dgst_derive_generated_by_verifies := 
forall (pubkey_pre: Z) (dgst_pre: Z) (signature_pre: Z) (SigS_generated: Z) (SigR_generated: Z) (P_generated: ec_point) (DigestBytes_generated: (@list Z)) (D_2: Z) ,
  (store_sm2_signature signature_pre SigR_generated SigS_generated )
  **  (store_bytes dgst_pre 32 DigestBytes_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_verify_dgst_globals )
|--
EX (DigestBytes_verifies: (@list Z)) (P_verifies: ec_point) (SigR_verifies: Z) (SigS_verifies: Z) ,
  (“ (P_verifies <> ECInfinity) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals ))
  **
  (((EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies ) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value (DigestBytes_verifies)) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature signature_pre SigR_verifies SigS_verifies )
  **  (store_bytes dgst_pre 32 DigestBytes_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )))
  -*
  ((EX D retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_sm2_keypair D P_generated ) ” 
  &&  “ (sm2_signature_generated (be_u8_list_value (DigestBytes_generated)) D SigR_generated SigS_generated ) ”
  &&  (store_sm2_signature signature_pre SigR_generated SigS_generated )
  **  (store_bytes dgst_pre 32 DigestBytes_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_verify_dgst_globals ))
  ||
  (EX retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~(exists (D_2: Z) , ((valid_sm2_keypair D_2 P_generated ) /\ (sm2_signature_generated (be_u8_list_value (DigestBytes_generated)) D_2 SigR_generated SigS_generated ))) ”
  &&  (store_sm2_signature signature_pre SigR_generated SigS_generated )
  **  (store_bytes dgst_pre 32 DigestBytes_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_verify_dgst_globals ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_point_facts_Strategy_Correct.
Include ecc_point_overwrite_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.
Include byte_memory_views_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_verify_dgst_safety_wit_1 : sm2_verify_dgst_safety_wit_1.
Axiom proof_of_sm2_verify_dgst_safety_wit_2 : sm2_verify_dgst_safety_wit_2.
Axiom proof_of_sm2_verify_dgst_safety_wit_3 : sm2_verify_dgst_safety_wit_3.
Axiom proof_of_sm2_verify_dgst_safety_wit_4 : sm2_verify_dgst_safety_wit_4.
Axiom proof_of_sm2_verify_dgst_safety_wit_5 : sm2_verify_dgst_safety_wit_5.
Axiom proof_of_sm2_verify_dgst_safety_wit_6 : sm2_verify_dgst_safety_wit_6.
Axiom proof_of_sm2_verify_dgst_safety_wit_7 : sm2_verify_dgst_safety_wit_7.
Axiom proof_of_sm2_verify_dgst_safety_wit_8 : sm2_verify_dgst_safety_wit_8.
Axiom proof_of_sm2_verify_dgst_safety_wit_9 : sm2_verify_dgst_safety_wit_9.
Axiom proof_of_sm2_verify_dgst_safety_wit_10 : sm2_verify_dgst_safety_wit_10.
Axiom proof_of_sm2_verify_dgst_safety_wit_11 : sm2_verify_dgst_safety_wit_11.
Axiom proof_of_sm2_verify_dgst_safety_wit_12 : sm2_verify_dgst_safety_wit_12.
Axiom proof_of_sm2_verify_dgst_safety_wit_13 : sm2_verify_dgst_safety_wit_13.
Axiom proof_of_sm2_verify_dgst_safety_wit_14 : sm2_verify_dgst_safety_wit_14.
Axiom proof_of_sm2_verify_dgst_safety_wit_15 : sm2_verify_dgst_safety_wit_15.
Axiom proof_of_sm2_verify_dgst_safety_wit_16 : sm2_verify_dgst_safety_wit_16.
Axiom proof_of_sm2_verify_dgst_safety_wit_17 : sm2_verify_dgst_safety_wit_17.
Axiom proof_of_sm2_verify_dgst_safety_wit_18 : sm2_verify_dgst_safety_wit_18.
Axiom proof_of_sm2_verify_dgst_safety_wit_19 : sm2_verify_dgst_safety_wit_19.
Axiom proof_of_sm2_verify_dgst_safety_wit_20 : sm2_verify_dgst_safety_wit_20.
Axiom proof_of_sm2_verify_dgst_safety_wit_21 : sm2_verify_dgst_safety_wit_21.
Axiom proof_of_sm2_verify_dgst_safety_wit_22 : sm2_verify_dgst_safety_wit_22.
Axiom proof_of_sm2_verify_dgst_safety_wit_23 : sm2_verify_dgst_safety_wit_23.
Axiom proof_of_sm2_verify_dgst_safety_wit_24 : sm2_verify_dgst_safety_wit_24.
Axiom proof_of_sm2_verify_dgst_safety_wit_25 : sm2_verify_dgst_safety_wit_25.
Axiom proof_of_sm2_verify_dgst_entail_wit_1 : sm2_verify_dgst_entail_wit_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_2 : sm2_verify_dgst_entail_wit_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_3 : sm2_verify_dgst_entail_wit_3.
Axiom proof_of_sm2_verify_dgst_entail_wit_4 : sm2_verify_dgst_entail_wit_4.
Axiom proof_of_sm2_verify_dgst_entail_wit_5 : sm2_verify_dgst_entail_wit_5.
Axiom proof_of_sm2_verify_dgst_entail_wit_6 : sm2_verify_dgst_entail_wit_6.
Axiom proof_of_sm2_verify_dgst_entail_wit_7_1 : sm2_verify_dgst_entail_wit_7_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_7_2 : sm2_verify_dgst_entail_wit_7_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_1 : sm2_verify_dgst_entail_wit_8_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_2 : sm2_verify_dgst_entail_wit_8_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_3 : sm2_verify_dgst_entail_wit_8_3.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_4 : sm2_verify_dgst_entail_wit_8_4.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_5 : sm2_verify_dgst_entail_wit_8_5.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_6 : sm2_verify_dgst_entail_wit_8_6.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_7 : sm2_verify_dgst_entail_wit_8_7.
Axiom proof_of_sm2_verify_dgst_entail_wit_8_8 : sm2_verify_dgst_entail_wit_8_8.
Axiom proof_of_sm2_verify_dgst_entail_wit_9_1 : sm2_verify_dgst_entail_wit_9_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_9_2 : sm2_verify_dgst_entail_wit_9_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_10_1 : sm2_verify_dgst_entail_wit_10_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_10_2 : sm2_verify_dgst_entail_wit_10_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_11_1 : sm2_verify_dgst_entail_wit_11_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_11_2 : sm2_verify_dgst_entail_wit_11_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_12_1 : sm2_verify_dgst_entail_wit_12_1.
Axiom proof_of_sm2_verify_dgst_entail_wit_12_2 : sm2_verify_dgst_entail_wit_12_2.
Axiom proof_of_sm2_verify_dgst_entail_wit_13 : sm2_verify_dgst_entail_wit_13.
Axiom proof_of_sm2_verify_dgst_return_wit_1 : sm2_verify_dgst_return_wit_1.
Axiom proof_of_sm2_verify_dgst_return_wit_2 : sm2_verify_dgst_return_wit_2.
Axiom proof_of_sm2_verify_dgst_return_wit_3 : sm2_verify_dgst_return_wit_3.
Axiom proof_of_sm2_verify_dgst_return_wit_4 : sm2_verify_dgst_return_wit_4.
Axiom proof_of_sm2_verify_dgst_return_wit_5 : sm2_verify_dgst_return_wit_5.
Axiom proof_of_sm2_verify_dgst_return_wit_6 : sm2_verify_dgst_return_wit_6.
Axiom proof_of_sm2_verify_dgst_return_wit_7 : sm2_verify_dgst_return_wit_7.
Axiom proof_of_sm2_verify_dgst_return_wit_8 : sm2_verify_dgst_return_wit_8.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_1 : sm2_verify_dgst_partial_solve_wit_1.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_2 : sm2_verify_dgst_partial_solve_wit_2.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_3 : sm2_verify_dgst_partial_solve_wit_3.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_4 : sm2_verify_dgst_partial_solve_wit_4.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_5 : sm2_verify_dgst_partial_solve_wit_5.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_6 : sm2_verify_dgst_partial_solve_wit_6.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_7 : sm2_verify_dgst_partial_solve_wit_7.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_8 : sm2_verify_dgst_partial_solve_wit_8.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_9 : sm2_verify_dgst_partial_solve_wit_9.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_10 : sm2_verify_dgst_partial_solve_wit_10.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_11_pure : sm2_verify_dgst_partial_solve_wit_11_pure.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_11 : sm2_verify_dgst_partial_solve_wit_11.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_12 : sm2_verify_dgst_partial_solve_wit_12.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_13 : sm2_verify_dgst_partial_solve_wit_13.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_14 : sm2_verify_dgst_partial_solve_wit_14.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_15_pure : sm2_verify_dgst_partial_solve_wit_15_pure.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_15 : sm2_verify_dgst_partial_solve_wit_15.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_16_pure : sm2_verify_dgst_partial_solve_wit_16_pure.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_16 : sm2_verify_dgst_partial_solve_wit_16.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_17 : sm2_verify_dgst_partial_solve_wit_17.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_18_pure : sm2_verify_dgst_partial_solve_wit_18_pure.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_18 : sm2_verify_dgst_partial_solve_wit_18.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_19_pure : sm2_verify_dgst_partial_solve_wit_19_pure.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_19 : sm2_verify_dgst_partial_solve_wit_19.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_20_pure : sm2_verify_dgst_partial_solve_wit_20_pure.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_20 : sm2_verify_dgst_partial_solve_wit_20.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_21 : sm2_verify_dgst_partial_solve_wit_21.
Axiom proof_of_sm2_verify_dgst_partial_solve_wit_22 : sm2_verify_dgst_partial_solve_wit_22.
Axiom proof_of_sm2_verify_dgst_derive_generated_by_verifies : sm2_verify_dgst_derive_generated_by_verifies.

End VC_Correct.
