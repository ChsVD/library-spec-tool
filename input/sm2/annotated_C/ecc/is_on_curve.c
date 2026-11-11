/* Verification copy of YCrypt/sm2/ecc.c::is_on_curve. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */

bool equ_to_AFPoint_one(const AFPoint* point)
/*@ base
    With X Y
    Require
      store_afpoint_fields(point, X, Y)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && X == 0 && Y == 0) ||
       (__return == 0 && (X != 0 || Y != 0))) &&
      store_afpoint_fields(point, X, Y)
 */
/*@ point
    With (P : ec_point)
    Require
      store_afpoint(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_afpoint(point, P)
 */;

void pow_mod_p(const u32* x, u32* result)
/*@ non_alias
    With X
    Require
      store_fp(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(result, Zmod(X * X, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */;

void mul_mod_p(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fp(x, X) *
      store_fp(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(y, Y) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_y
    With X Y
    Require
      result == y &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == y &&
      store_fp(x, X) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) *
      store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(b, B) *
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_sm2_p
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_fp(b, B) *
      store_sm2_p
 */;

bool u32_eq(const u32 *a, const u32 *b)
/*@ With (A B : Z)
    Require
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == B) ||
       (__return == 0 && A != B)) &&
      store_u256(a, A) *
      store_u256(b, B)
 */;

bool is_on_curve(const AFPoint* point)
/*@ With X Y
    Require
      store_afpoint_fields(point, X, Y) *
      store_sm2_a *
      store_sm2_b *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && valid_afpoint(X, Y)) ||
       (__return == 0 && (! valid_afpoint(X, Y)))) &&
      store_afpoint_fields(point, X, Y) *
      store_sm2_a *
      store_sm2_b *
      store_sm2_p *
      store_sm2_rhop
 */
{
	if (equ_to_AFPoint_one(point) /*@ where (base) */)
		return true;

	u32 y2, x3, ax, res;
	pow_mod_p(&point->y, &y2) /*@ where (non_alias) */;
	pow_mod_p(&point->x, &x3) /*@ where (non_alias) */;
	mul_mod_p(&point->x, &x3, &x3) /*@ where (r_eq_y) */;
	/*@ do open_sm2_a */
	mul_mod_p(&SM2_a, &point->x, &ax) /*@ where (non_alias) */;
	add_mod_p(&x3, &ax, &res) /*@ where (non_alias) */;
	/*@ do open_sm2_b */
	add_mod_p(&res, &SM2_b, &res) /*@ where (r_eq_a) */;

	return u32_eq(&y2, &res);
}
