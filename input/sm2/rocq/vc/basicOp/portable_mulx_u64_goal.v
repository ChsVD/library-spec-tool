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

(*----- Function portable_mulx_u64 -----*)

Definition portable_mulx_u64_safety_wit_1 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < U64_MOD)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre < U64_MOD)) ,
  ((( &( "a_hi" ) )) # UInt  |->_)
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_2 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < U64_MOD)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre < U64_MOD)) ,
  ((( &( "a_hi" ) )) # UInt  |->_)
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_3 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < U64_MOD)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre < U64_MOD)) ,
  ((( &( "b_hi" ) )) # UInt  |->_)
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_4 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre < U64_MOD)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre < U64_MOD)) ,
  ((( &( "b_hi" ) )) # UInt  |->_)
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_5 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_carry" ) )) # UChar  |->_)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition portable_mulx_u64_safety_wit_6 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_carry" ) )) # UChar  |->_)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition portable_mulx_u64_safety_wit_7 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_lo" ) )) # UInt64  |->_)
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_8 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_lo" ) )) # UInt64  |->_)
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_9 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_lo" ) )) # UInt64  |->_)
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_10 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_lo" ) )) # UInt64  |->_)
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_11 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_12 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_13 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_14 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_15 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_16 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= 63) ” 
  &&  “ (0 <= 32) ”
.

Definition portable_mulx_u64_safety_wit_17 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_18 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre < U64_MOD)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre < U64_MOD)) ,
  ((( &( "mid_hi" ) )) # UInt64  |->_)
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition portable_mulx_u64_safety_wit_19 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((( &( "lo_carry" ) )) # UChar  |->_)
  **  ((( &( "mid_hi" ) )) # UInt64  |-> (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)))
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition portable_mulx_u64_safety_wit_20 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((( &( "lo_carry" ) )) # UChar  |->_)
  **  ((( &( "mid_hi" ) )) # UInt64  |-> (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)))
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 1)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition portable_mulx_u64_safety_wit_21 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((( &( "lo_carry" ) )) # UChar  |->_)
  **  ((( &( "mid_hi" ) )) # UInt64  |-> (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)))
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition portable_mulx_u64_safety_wit_22 := 
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((( &( "lo_carry" ) )) # UChar  |->_)
  **  ((( &( "mid_hi" ) )) # UInt64  |-> (unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)))
  **  ((( &( "mid_lo" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))
  **  ((( &( "mid_carry" ) )) # UChar  |-> 0)
  **  ((( &( "mid" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)))
  **  ((( &( "hi" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "lo" ) )) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
  **  ((( &( "p3" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p2" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "p1" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))
  **  ((( &( "p0" ) )) # UInt64  |-> ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ))
  **  ((( &( "b_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)))
  **  ((( &( "b_lo" ) )) # UInt  |-> (unsigned_last_nbits (b_pre) (32)))
  **  ((( &( "a_hi" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)))
  **  ((( &( "a_lo" ) )) # UInt  |-> (unsigned_last_nbits (a_pre) (32)))
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "hi_ptr" ) )) # Ptr  |-> hi_ptr_pre)
  **  ((hi_ptr_pre) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition portable_mulx_u64_return_wit_1 := 
(
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((hi_ptr_pre) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64)))
|--
  EX (hi: Z) ,
  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi < U64_MOD) ” 
  &&  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + (hi * U64_MOD ) )) ”
  &&  ((hi_ptr_pre) # UInt64  |-> hi)
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64)) * U64_MOD ) )) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ”
  &&  emp
).

Definition portable_mulx_u64_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64)) * U64_MOD ) ))
.

Definition portable_mulx_u64_return_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_1_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 1 )) (64)) )) (64)))
.

Definition portable_mulx_u64_return_wit_1_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_1_split_goal_5 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
.

Definition portable_mulx_u64_return_wit_2 := 
(
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((hi_ptr_pre) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64)))
|--
  EX (hi: Z) ,
  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi < U64_MOD) ” 
  &&  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + (hi * U64_MOD ) )) ”
  &&  ((hi_ptr_pre) # UInt64  |-> hi)
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64)) * U64_MOD ) )) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ”
  &&  emp
).

Definition portable_mulx_u64_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64)) * U64_MOD ) ))
.

Definition portable_mulx_u64_return_wit_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_2_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 1 32) )) (64)) + 0 ) )) (64)))
.

Definition portable_mulx_u64_return_wit_2_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_2_split_goal_5 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) < ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
.

Definition portable_mulx_u64_return_wit_3 := 
(
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((hi_ptr_pre) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64)))
|--
  EX (hi: Z) ,
  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi < U64_MOD) ” 
  &&  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + (hi * U64_MOD ) )) ”
  &&  ((hi_ptr_pre) # UInt64  |-> hi)
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64)) * U64_MOD ) )) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ”
  &&  emp
).

Definition portable_mulx_u64_return_wit_3_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64)) * U64_MOD ) ))
.

Definition portable_mulx_u64_return_wit_3_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_3_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + (unsigned_last_nbits (((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 1 )) (64)) )) (64)))
.

Definition portable_mulx_u64_return_wit_3_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_3_split_goal_5 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
.

Definition portable_mulx_u64_return_wit_4 := 
(
forall (hi_ptr_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((hi_ptr_pre) # UInt64  |-> (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64)))
|--
  EX (hi: Z) ,
  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= hi) ” 
  &&  “ (hi < U64_MOD) ” 
  &&  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + (hi * U64_MOD ) )) ”
  &&  ((hi_ptr_pre) # UInt64  |-> hi)
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  TT && emp 
|--
  “ ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64)) * U64_MOD ) )) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD) ” 
  &&  “ (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64))) ”
  &&  emp
).

Definition portable_mulx_u64_return_wit_4_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((a_pre * b_pre ) = ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) + ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64)) * U64_MOD ) ))
.

Definition portable_mulx_u64_return_wit_4_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_4_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits (((Z.shiftr (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32) + (Z.shiftl 0 32) )) (64)) + 0 ) )) (64)))
.

Definition portable_mulx_u64_return_wit_4_split_goal_4 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) < U64_MOD)
.

Definition portable_mulx_u64_return_wit_4_split_goal_5 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)) >= (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)))) (PreH2 : ((unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) >= ((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ))) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre < U64_MOD)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre < U64_MOD)) ,
  (0 <= (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits (b_pre) (32)) ) + (unsigned_last_nbits ((Z.shiftl (unsigned_last_nbits ((((unsigned_last_nbits (a_pre) (32)) * (unsigned_last_nbits ((Z.shiftr b_pre 32)) (32)) ) + ((unsigned_last_nbits ((Z.shiftr a_pre 32)) (32)) * (unsigned_last_nbits (b_pre) (32)) ) )) (64)) 32)) (64)) )) (64)))
.

Module Type VC_Correct.


Axiom proof_of_portable_mulx_u64_safety_wit_1 : portable_mulx_u64_safety_wit_1.
Axiom proof_of_portable_mulx_u64_safety_wit_2 : portable_mulx_u64_safety_wit_2.
Axiom proof_of_portable_mulx_u64_safety_wit_3 : portable_mulx_u64_safety_wit_3.
Axiom proof_of_portable_mulx_u64_safety_wit_4 : portable_mulx_u64_safety_wit_4.
Axiom proof_of_portable_mulx_u64_safety_wit_5 : portable_mulx_u64_safety_wit_5.
Axiom proof_of_portable_mulx_u64_safety_wit_6 : portable_mulx_u64_safety_wit_6.
Axiom proof_of_portable_mulx_u64_safety_wit_7 : portable_mulx_u64_safety_wit_7.
Axiom proof_of_portable_mulx_u64_safety_wit_8 : portable_mulx_u64_safety_wit_8.
Axiom proof_of_portable_mulx_u64_safety_wit_9 : portable_mulx_u64_safety_wit_9.
Axiom proof_of_portable_mulx_u64_safety_wit_10 : portable_mulx_u64_safety_wit_10.
Axiom proof_of_portable_mulx_u64_safety_wit_11 : portable_mulx_u64_safety_wit_11.
Axiom proof_of_portable_mulx_u64_safety_wit_12 : portable_mulx_u64_safety_wit_12.
Axiom proof_of_portable_mulx_u64_safety_wit_13 : portable_mulx_u64_safety_wit_13.
Axiom proof_of_portable_mulx_u64_safety_wit_14 : portable_mulx_u64_safety_wit_14.
Axiom proof_of_portable_mulx_u64_safety_wit_15 : portable_mulx_u64_safety_wit_15.
Axiom proof_of_portable_mulx_u64_safety_wit_16 : portable_mulx_u64_safety_wit_16.
Axiom proof_of_portable_mulx_u64_safety_wit_17 : portable_mulx_u64_safety_wit_17.
Axiom proof_of_portable_mulx_u64_safety_wit_18 : portable_mulx_u64_safety_wit_18.
Axiom proof_of_portable_mulx_u64_safety_wit_19 : portable_mulx_u64_safety_wit_19.
Axiom proof_of_portable_mulx_u64_safety_wit_20 : portable_mulx_u64_safety_wit_20.
Axiom proof_of_portable_mulx_u64_safety_wit_21 : portable_mulx_u64_safety_wit_21.
Axiom proof_of_portable_mulx_u64_safety_wit_22 : portable_mulx_u64_safety_wit_22.
Axiom proof_of_portable_mulx_u64_return_wit_1 : portable_mulx_u64_return_wit_1.
Axiom proof_of_portable_mulx_u64_return_wit_2 : portable_mulx_u64_return_wit_2.
Axiom proof_of_portable_mulx_u64_return_wit_3 : portable_mulx_u64_return_wit_3.
Axiom proof_of_portable_mulx_u64_return_wit_4 : portable_mulx_u64_return_wit_4.

End VC_Correct.
