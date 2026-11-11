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
From SimpleC.EE.Applications_human.sm2.vc.extra Require Import str_reverse_in_place_goal.
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

Lemma proof_of_str_reverse_in_place_safety_wit_1 : str_reverse_in_place_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_str_reverse_in_place_entail_wit_1 : str_reverse_in_place_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_str_reverse_in_place_partial_solve_wit_1 : str_reverse_in_place_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_str_reverse_in_place_partial_solve_wit_2 : str_reverse_in_place_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_str_reverse_in_place_partial_solve_wit_3 : str_reverse_in_place_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_str_reverse_in_place_partial_solve_wit_4 : str_reverse_in_place_partial_solve_wit_4.
Proof. Admitted. 

