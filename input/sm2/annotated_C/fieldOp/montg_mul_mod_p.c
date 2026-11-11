/* Verification copy of YCrypt/sm2/fieldOp.c::montg_mul_mod_p. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

void sm2p_mong_mul(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_u256(x, X) *
      store_u256(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_u256(y, Y) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == x &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_u256(y, Y) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_y
    With X Y
    Require
      result == y &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == y &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_u256(a, A) *
      store_u256(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * B + K * SM2_P_Z &&
        store_u256(a, A) *
        store_u256(b, B) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_u256(a, A) *
      store_u256(b, B) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == a &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * B + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_u256(b, B) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_u256(a, A) *
      store_u256(b, B) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == b &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * B + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias <= non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_r_eq_a <= r_eq_a
    With A B
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, mont_p(A * B)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_r_eq_b <= r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias */
/*@ r_eq_a */
/*@ r_eq_b */
{
	sm2p_mong_mul(a, b, result)
	/*@
	  where (non_alias) X = A_non_alias, Y = B_non_alias
	    $ non_alias
	  where (r_eq_x) X = A_r_eq_a, Y = B_r_eq_a
	    $ r_eq_a
	  where (r_eq_y) X = A_r_eq_b, Y = B_r_eq_b
	    $ r_eq_b
	 */;
}
