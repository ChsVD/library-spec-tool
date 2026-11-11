(** Approved C-layout bridges not exported by the QCP front end. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.Applications_human.sm2.lib Require Import ecc_point_def.

Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(** [AFPoint] contains two four-limb [u32] fields.  QCP represents the
    typedef size abstractly, while the generated structure-array instance
    computes its element size from those fields. *)
Axiom sizeof_AFPoint_layout :
  sizeof("AFPoint") = 64.

Lemma sizeof_AFPoint_matches_generated :
  sizeof("AFPoint") = StoreStructAFPointAsElement.sizeA.
Proof.
  rewrite sizeof_AFPoint_layout.
  unfold StoreStructAFPointAsElement.sizeA,
    StoreStructu32AsElement.sizeA.
  rewrite sizeof_uint64.
  reflexivity.
Qed.

(** [AFPoint.x] is the first field of the structure.  QCP keeps named
    field addresses abstract, so this equality connects the C zero-offset
    layout fact to the address of an [AFPoint] object. *)
Axiom afpoint_x_field_address_eq :
  forall address : addr,
    &(address # "AFPoint" ->ₛ "x") = address.

(** The frontend may print [point->field.v] directly or through the
    address of the embedded [u32]. *)
Lemma nested_afpoint_u32_v_addr_eq :
  forall (point : Z) (field : string),
    &((point) # "AFPoint" ->ₛ field .ₛ "v") =
    &(((&(point # "AFPoint" ->ₛ field))) # "u32" ->ₛ "v").
Proof.
  intros.
  csimpl.
  reflexivity.
Qed.

(** The corresponding normalization for a named [AFPoint] object. *)
Lemma named_afpoint_u32_v_addr_eq :
  forall (name field : string),
    eval_addr_expr
      (RE_addr_of
        (LE_dot_field
          (LE_arrow_field (RE_addr_of (LE_var name)) field)
          "v")) =
    eval_addr_expr
      (RE_addr_of
        (LE_dot_field
          (LE_arrow_field
            (RE_const
              (eval_addr_expr (RE_addr_of (LE_var name)))
              (FET_alias "AFPoint"))
            field)
          "v")).
Proof.
  intros.
  csimpl.
  reflexivity.
Qed.

(** [_SM3_CTX.block] starts eight bytes after [_SM3_CTX.nblocks].
    QCP keeps named field addresses abstract, so this layout equality is
    the minimal bridge needed for the internal [block] and [block + 56]
    word views. *)
Axiom sm3_block_count_address_eq :
  forall ctx : addr,
    &(ctx # "_SM3_CTX" ->ₛ "block") + 56 =
      &(ctx # "_SM3_CTX" ->ₛ "nblocks") + 64.
