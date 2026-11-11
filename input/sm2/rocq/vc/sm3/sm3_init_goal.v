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
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm3_ctx_views_strategy_proof.

(*----- Function sm3_init -----*)

Definition sm3_init_safety_wit_1 := 
forall (ctx_pre: Z) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (UIntArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_init_safety_wit_2 := 
forall (ctx_pre: Z) ,
  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  (UIntArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (1937774191 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1937774191) ”
.

Definition sm3_init_safety_wit_3 := 
forall (ctx_pre: Z) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 1 8 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm3_init_safety_wit_4 := 
forall (ctx_pre: Z) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 1 8 )
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (1226093241 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1226093241) ”
.

Definition sm3_init_safety_wit_5 := 
forall (ctx_pre: Z) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (1 + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sm3_init_safety_wit_6 := 
forall (ctx_pre: Z) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (1 + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (388252375 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 388252375) ”
.

Definition sm3_init_safety_wit_7 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((1 + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sm3_init_safety_wit_8 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((1 + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition sm3_init_safety_wit_9 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((((1 + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition sm3_init_safety_wit_10 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((((1 + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (372324522 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 372324522) ”
.

Definition sm3_init_safety_wit_11 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition sm3_init_safety_wit_12 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition sm3_init_safety_wit_13 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_init_safety_wit_14 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((( &( "ctx" ) )) # Ptr  |-> ctx_pre)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> 0)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm3_init_return_wit_1 := 
(
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |-> 0)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |-> 0)
|--
  (store_sm3_ctx ctx_pre (@nil Z) )
) \/
(
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (u8_list_bounded (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) < SM3_MAX_BYTES) ” 
  &&  “ (0 = ((Zlength ((@nil Z))) ÷ 64 )) ” 
  &&  “ (0 = (Zlength ((sm3_tail ((@nil Z)))))) ” 
  &&  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((@nil Z))))))) = 8) ” 
  &&  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((@nil Z))))) ) ” 
  &&  “ (0 <= (Zlength ((sm3_tail ((@nil Z)))))) ” 
  &&  “ ((Zlength ((sm3_tail ((@nil Z))))) <= 64) ” 
  &&  “ (u8_list_bounded (sm3_tail ((@nil Z))) ) ”
  &&  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail ((@nil Z))))) ) (64 - (Zlength ((sm3_tail ((@nil Z))))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail ((@nil Z))))) (sm3_tail ((@nil Z))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((@nil Z))))) )
).

Definition sm3_init_return_wit_1_split_goal_1 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (u8_list_bounded (@nil Z) ) ”
.

Definition sm3_init_return_wit_1_split_goal_2 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ ((Zlength ((@nil Z))) < SM3_MAX_BYTES) ”
.

Definition sm3_init_return_wit_1_split_goal_3 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (0 = ((Zlength ((@nil Z))) ÷ 64 )) ”
.

Definition sm3_init_return_wit_1_split_goal_4 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (0 = (Zlength ((sm3_tail ((@nil Z)))))) ”
.

Definition sm3_init_return_wit_1_split_goal_5 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ ((Zlength ((sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((@nil Z))))))) = 8) ”
.

Definition sm3_init_return_wit_1_split_goal_6 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (limb_list_bounded SM3_WORD_MODULUS (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((@nil Z))))) ) ”
.

Definition sm3_init_return_wit_1_split_goal_7 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (0 <= (Zlength ((sm3_tail ((@nil Z)))))) ”
.

Definition sm3_init_return_wit_1_split_goal_8 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ ((Zlength ((sm3_tail ((@nil Z))))) <= 64) ”
.

Definition sm3_init_return_wit_1_split_goal_9 := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  “ (u8_list_bounded (sm3_tail ((@nil Z))) ) ”
.

Definition sm3_init_return_wit_1_split_goal_spatial := 
forall (ctx_pre: Z) (PreH1 : (1937774191 <= UINT_MAX)) (PreH2 : (1226093241 <= UINT_MAX)) (PreH3 : (388252375 <= UINT_MAX)) (PreH4 : (3666478592 <= UINT_MAX)) (PreH5 : (2842636476 <= UINT_MAX)) (PreH6 : (372324522 <= UINT_MAX)) (PreH7 : (3817729613 <= UINT_MAX)) (PreH8 : (2969243214 <= UINT_MAX)) (PreH9 : (1937774191 >= 0)) (PreH10 : (1226093241 >= 0)) (PreH11 : (388252375 >= 0)) (PreH12 : (3666478592 >= 0)) (PreH13 : (2842636476 >= 0)) (PreH14 : (372324522 >= 0)) (PreH15 : (3817729613 >= 0)) (PreH16 : (2969243214 >= 0)) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |-> 2969243214)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
|--
  (UCharArray.undef_full (&((ctx_pre)  # "_SM3_CTX" ->ₛ "block") + (Zlength ((sm3_tail ((@nil Z))))) ) (64 - (Zlength ((sm3_tail ((@nil Z))))) ) )
  **  (UCharArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") (Zlength ((sm3_tail ((@nil Z))))) (sm3_tail ((@nil Z))) )
  **  (UIntArray.full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 (sm3_compress_bytes (SM3_IV) ((sm3_full_bytes ((@nil Z))))) )
.

Definition sm3_init_partial_solve_wit_1 := 
forall (ctx_pre: Z) ,
  (undef_sm3_ctx ctx_pre )
|--
  (undef_sm3_ctx ctx_pre )
.

Definition sm3_init_partial_solve_wit_2 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 1 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_3 := 
forall (ctx_pre: Z) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 1 8 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (1 + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_4 := 
forall (ctx_pre: Z) ,
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (1 + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 2 (1 + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_5 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((1 + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 3 ((1 + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_6 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((1 + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 4 (((1 + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_7 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((((1 + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 5 ((((1 + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_8 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") (((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 6 (((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_partial_solve_wit_9 := 
forall (ctx_pre: Z) ,
  (UIntArray.undef_seg &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") ((((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
|--
  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (7 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i &((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") 7 ((((((1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) 8 )
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (6 * sizeof(UINT)))) # UInt  |-> 3817729613)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (5 * sizeof(UINT)))) # UInt  |-> 372324522)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (4 * sizeof(UINT)))) # UInt  |-> 2842636476)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (3 * sizeof(UINT)))) # UInt  |-> 3666478592)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (2 * sizeof(UINT)))) # UInt  |-> 388252375)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (1 * sizeof(UINT)))) # UInt  |-> 1226093241)
  **  (((&((ctx_pre)  # "_SM3_CTX" ->ₛ "digest") + (0 * sizeof(UINT)))) # UInt  |-> 1937774191)
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx_pre)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx_pre)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Definition sm3_init_which_implies_wit_1 := 
forall (ctx: Z) ,
  (undef_sm3_ctx ctx )
|--
  (UIntArray.undef_full &((ctx)  # "_SM3_CTX" ->ₛ "digest") 8 )
  **  ((&((ctx)  # "_SM3_CTX" ->ₛ "nblocks")) # UInt64  |->_)
  **  (UCharArray.undef_full &((ctx)  # "_SM3_CTX" ->ₛ "block") 64 )
  **  ((&((ctx)  # "_SM3_CTX" ->ₛ "num")) # UInt64  |->_)
.

Module Type VC_Correct.

Include byte_memory_views_Strategy_Correct.
Include sm3_ctx_views_Strategy_Correct.

Axiom proof_of_sm3_init_safety_wit_1 : sm3_init_safety_wit_1.
Axiom proof_of_sm3_init_safety_wit_2 : sm3_init_safety_wit_2.
Axiom proof_of_sm3_init_safety_wit_3 : sm3_init_safety_wit_3.
Axiom proof_of_sm3_init_safety_wit_4 : sm3_init_safety_wit_4.
Axiom proof_of_sm3_init_safety_wit_5 : sm3_init_safety_wit_5.
Axiom proof_of_sm3_init_safety_wit_6 : sm3_init_safety_wit_6.
Axiom proof_of_sm3_init_safety_wit_7 : sm3_init_safety_wit_7.
Axiom proof_of_sm3_init_safety_wit_8 : sm3_init_safety_wit_8.
Axiom proof_of_sm3_init_safety_wit_9 : sm3_init_safety_wit_9.
Axiom proof_of_sm3_init_safety_wit_10 : sm3_init_safety_wit_10.
Axiom proof_of_sm3_init_safety_wit_11 : sm3_init_safety_wit_11.
Axiom proof_of_sm3_init_safety_wit_12 : sm3_init_safety_wit_12.
Axiom proof_of_sm3_init_safety_wit_13 : sm3_init_safety_wit_13.
Axiom proof_of_sm3_init_safety_wit_14 : sm3_init_safety_wit_14.
Axiom proof_of_sm3_init_return_wit_1 : sm3_init_return_wit_1.
Axiom proof_of_sm3_init_partial_solve_wit_1 : sm3_init_partial_solve_wit_1.
Axiom proof_of_sm3_init_partial_solve_wit_2 : sm3_init_partial_solve_wit_2.
Axiom proof_of_sm3_init_partial_solve_wit_3 : sm3_init_partial_solve_wit_3.
Axiom proof_of_sm3_init_partial_solve_wit_4 : sm3_init_partial_solve_wit_4.
Axiom proof_of_sm3_init_partial_solve_wit_5 : sm3_init_partial_solve_wit_5.
Axiom proof_of_sm3_init_partial_solve_wit_6 : sm3_init_partial_solve_wit_6.
Axiom proof_of_sm3_init_partial_solve_wit_7 : sm3_init_partial_solve_wit_7.
Axiom proof_of_sm3_init_partial_solve_wit_8 : sm3_init_partial_solve_wit_8.
Axiom proof_of_sm3_init_partial_solve_wit_9 : sm3_init_partial_solve_wit_9.
Axiom proof_of_sm3_init_which_implies_wit_1 : sm3_init_which_implies_wit_1.

End VC_Correct.
