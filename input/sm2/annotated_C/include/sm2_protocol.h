#ifndef SM2_PROTOCOL_H
#define SM2_PROTOCOL_H

#include "ecc.h"
#include "sm3.h"
#include "sm2_table.h"

extern const AFPoint SM2_G;

/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol
 */

/*@ Extern Coq
      (valid_sm2_private_key : Z -> Prop)
      (valid_sm2_keypair : Z -> ec_point -> Prop)
      (valid_sm2_public_key : ec_point -> Prop)
      (sm2_id_digest_output_aligned : Z -> Z -> Prop)
      (sm2_message_input_aligned : Z -> Z -> Prop)
      (sm2_point_x : ec_point -> Z)
      (sm2_point_y : ec_point -> Z)
      (be_u8_list_value : list Z -> Z)
      (u256_to_be_bytes : Z -> list Z)
      (sm2_entla_bytes : Z -> list Z)
      (sm2_za_input : list Z -> ec_point -> list Z)
      (sm2_za_digest : list Z -> ec_point -> list Z)
      (sm2_message_digest : list Z -> ec_point -> list Z -> list Z)
      (sm2_signature_generated : Z -> Z -> Z -> Z -> Prop)
      (sm2_signature_verifies : Z -> ec_point -> Z -> Z -> Prop)
      (undef_sm2_private_key : Z -> Assertion)
      (store_sm2_private_key : Z -> Z -> Assertion)
      (undef_sm2_signature : Z -> Assertion)
      (store_sm2_signature : Z -> Z -> Z -> Assertion)
      (store_sm2_public_key : Z -> ec_point -> Assertion)
      (store_sm2_za : Z -> list Z -> ec_point -> list Z -> Assertion)
      (store_sm2_g : Assertion)
      (store_sm2_get_public_key_globals : Assertion)
      (store_sm2_keypair_globals : Assertion)
      (store_sm2_za_globals : Assertion)
      (store_sm2_sign_dgst_globals : Assertion)
      (store_sm2_sign_globals : Assertion)
      (store_sm2_verify_dgst_globals : Assertion)
      (store_sm2_verify_globals : Assertion)
 */

#endif
