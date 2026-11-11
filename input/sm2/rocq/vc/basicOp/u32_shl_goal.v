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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.

(*----- Function u32_shl -----*)

Definition u32_shl_safety_wit_1 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition u32_shl_safety_wit_2 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_shl_safety_wit_3 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition u32_shl_safety_wit_4 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_shl_safety_wit_5 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition u32_shl_safety_wit_6 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition u32_shl_safety_wit_7 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition u32_shl_safety_wit_8 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_safety_wit_9 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_shl_safety_wit_10 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition u32_shl_safety_wit_11 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_shl_safety_wit_12 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition u32_shl_safety_wit_13 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition u32_shl_safety_wit_14 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition u32_shl_safety_wit_15 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_safety_wit_16 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_safety_wit_17 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition u32_shl_safety_wit_18 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_safety_wit_19 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= 63) ” 
  &&  “ (0 <= 63) ”
.

Definition u32_shl_safety_wit_20 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition u32_shl_safety_wit_21 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_safety_wit_22 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_safety_wit_23 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_shl_safety_wit_24 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition u32_shl_safety_wit_25 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition u32_shl_safety_wit_26 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= 63) ” 
  &&  “ (0 <= 1) ”
.

Definition u32_shl_safety_wit_27 := 
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((( &( "carry" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr x3 63)) (8)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition u32_shl_entail_wit_1 := 
forall (input_pre: Z) (X: Z) ,
  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (store_u256 input_pre X )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
.

Definition u32_shl_return_wit_1 := 
(
forall (input_pre: Z) (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (((&((input_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
  **  (((&((input_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
|--
  EX (Y: Z) ,
  “ (u256_shl_result X Y (unsigned_last_nbits ((Z.shiftr x3 63)) (8)) ) ”
  &&  (store_u256 input_pre Y )
) \/
(
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  TT && emp 
|--
  “ (u256_shl_result X (u256_of_limbs ((unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))) (unsigned_last_nbits ((Z.shiftr x3 63)) (8)) ) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD) ” 
  &&  “ (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63))) ” 
  &&  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD) ”
  &&  emp
).

Definition u32_shl_return_wit_1_split_goal_1 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (u256_shl_result X (u256_of_limbs ((unsigned_last_nbits ((Z.shiftl x0 1)) (64))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63))) ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))) (unsigned_last_nbits ((Z.shiftr x3 63)) (8)) )
.

Definition u32_shl_return_wit_1_split_goal_2 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (0 <= (unsigned_last_nbits ((Z.shiftl x0 1)) (64)))
.

Definition u32_shl_return_wit_1_split_goal_3 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((unsigned_last_nbits ((Z.shiftl x0 1)) (64)) < U64_MOD)
.

Definition u32_shl_return_wit_1_split_goal_4 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)))
.

Definition u32_shl_return_wit_1_split_goal_5 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl x1 1)) (64)) (Z.shiftr x0 63)) < U64_MOD)
.

Definition u32_shl_return_wit_1_split_goal_6 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)))
.

Definition u32_shl_return_wit_1_split_goal_7 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl x2 1)) (64)) (Z.shiftr x1 63)) < U64_MOD)
.

Definition u32_shl_return_wit_1_split_goal_8 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  (0 <= (Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)))
.

Definition u32_shl_return_wit_1_split_goal_9 := 
forall (X: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) ,
  ((Z.lor (unsigned_last_nbits ((Z.shiftl x3 1)) (64)) (Z.shiftr x2 63)) < U64_MOD)
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_u32_shl_safety_wit_1 : u32_shl_safety_wit_1.
Axiom proof_of_u32_shl_safety_wit_2 : u32_shl_safety_wit_2.
Axiom proof_of_u32_shl_safety_wit_3 : u32_shl_safety_wit_3.
Axiom proof_of_u32_shl_safety_wit_4 : u32_shl_safety_wit_4.
Axiom proof_of_u32_shl_safety_wit_5 : u32_shl_safety_wit_5.
Axiom proof_of_u32_shl_safety_wit_6 : u32_shl_safety_wit_6.
Axiom proof_of_u32_shl_safety_wit_7 : u32_shl_safety_wit_7.
Axiom proof_of_u32_shl_safety_wit_8 : u32_shl_safety_wit_8.
Axiom proof_of_u32_shl_safety_wit_9 : u32_shl_safety_wit_9.
Axiom proof_of_u32_shl_safety_wit_10 : u32_shl_safety_wit_10.
Axiom proof_of_u32_shl_safety_wit_11 : u32_shl_safety_wit_11.
Axiom proof_of_u32_shl_safety_wit_12 : u32_shl_safety_wit_12.
Axiom proof_of_u32_shl_safety_wit_13 : u32_shl_safety_wit_13.
Axiom proof_of_u32_shl_safety_wit_14 : u32_shl_safety_wit_14.
Axiom proof_of_u32_shl_safety_wit_15 : u32_shl_safety_wit_15.
Axiom proof_of_u32_shl_safety_wit_16 : u32_shl_safety_wit_16.
Axiom proof_of_u32_shl_safety_wit_17 : u32_shl_safety_wit_17.
Axiom proof_of_u32_shl_safety_wit_18 : u32_shl_safety_wit_18.
Axiom proof_of_u32_shl_safety_wit_19 : u32_shl_safety_wit_19.
Axiom proof_of_u32_shl_safety_wit_20 : u32_shl_safety_wit_20.
Axiom proof_of_u32_shl_safety_wit_21 : u32_shl_safety_wit_21.
Axiom proof_of_u32_shl_safety_wit_22 : u32_shl_safety_wit_22.
Axiom proof_of_u32_shl_safety_wit_23 : u32_shl_safety_wit_23.
Axiom proof_of_u32_shl_safety_wit_24 : u32_shl_safety_wit_24.
Axiom proof_of_u32_shl_safety_wit_25 : u32_shl_safety_wit_25.
Axiom proof_of_u32_shl_safety_wit_26 : u32_shl_safety_wit_26.
Axiom proof_of_u32_shl_safety_wit_27 : u32_shl_safety_wit_27.
Axiom proof_of_u32_shl_entail_wit_1 : u32_shl_entail_wit_1.
Axiom proof_of_u32_shl_return_wit_1 : u32_shl_return_wit_1.

End VC_Correct.
