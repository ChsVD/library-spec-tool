/* Verification copy of YCrypt/sm2/ecc.c::jacobian_to_affine. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */

bool u32_eq_zero(const u32 *a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) ||
       (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */;

bool equ_to_JPoint_one(const JPoint* point)
/*@ base
    With JX JY JZ
    Require
      store_jpoint_fields(point, JX, JY, JZ)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && JX == 1 && JY == 1 && JZ == 0) ||
       (__return == 0 && (JX != 1 || JY != 1 || JZ != 0))) &&
      store_jpoint_fields(point, JX, JY, JZ)
 */
/*@ point
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_jpoint_with_canonical_infinity(point, P)
 */;

void inv_for_mul_mod_p(const u32* input, u32* result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fp(input, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv,
        0 <= Ainv && Ainv < SM2_P_Z &&
        Zmod(A * Ainv, SM2_P_Z) == 1 &&
        store_fp(input, A) *
        store_fp(result, Ainv) *
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
/*@ x_eq_y
    With X
    Require
      x == y &&
      store_fp(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      x == y &&
      store_fp(x, X) *
      store_fp(result, Zmod(X * X, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */;

AFPoint* memset(AFPoint* dest, int c, size_t n)
/*@ Require
      c == 0 && n == 64 &&
      UInt64Array::undef_full(&(dest->x.v[0]), 4) *
      UInt64Array::undef_full(&(dest->y.v[0]), 4)
    Ensure
      __return == dest &&
      store_afpoint_fields(dest, 0, 0)
 */;

void jacobian_to_affine(const JPoint* point, AFPoint* result)
/*@ non_alias
    With JX JY JZ
    Require
      (JZ == 0 => canonical_jpoint_infinity(JX, JY, JZ)) &&
      store_jpoint_fields(point, JX, JY, JZ) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists RX RY,
        jpoint_to_afpoint_coordinates(JX, JY, JZ, RX, RY) &&
        store_jpoint_fields(point, JX, JY, JZ) *
        store_afpoint_fields(result, RX, RY) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void jacobian_to_affine(const JPoint* point, AFPoint* result)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_jpoint_with_canonical_infinity(point, P) *
      store_afpoint(result, P) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void jacobian_to_affine(const JPoint* point, AFPoint* result)
/*@ non_alias */
{
	u32 u, u_square, u_cube;
	/*@ Branch name non_alias */
	if (!u32_eq_zero(&point->z))
	{
		inv_for_mul_mod_p(&point->z, &u)
		/*@
		  where (non_alias) A = JZ_non_alias
		    $ non_alias
		 */;
		/*@ Given Ainv $ non_alias */
		mul_mod_p(&u, &u, &u_square)
		/*@
		  where (x_eq_y) X = Ainv
		    $ non_alias
		 */;
		mul_mod_p(&u_square, &u, &u_cube)
		/*@
		  where (non_alias) X = Zmod(Ainv * Ainv, SM2_P_Z), Y = Ainv
		    $ non_alias
		 */;

		mul_mod_p(&point->x, &u_square, &result->x)
		/*@
		  where (non_alias) X = JX_non_alias,
		                    Y = Zmod(Ainv * Ainv, SM2_P_Z)
		    $ non_alias
		 */;
		mul_mod_p(&point->y, &u_cube, &result->y)
		/*@
		  where (non_alias) X = JY_non_alias,
		                    Y = Zmod(Zmod(Ainv * Ainv, SM2_P_Z) * Ainv,
		                             SM2_P_Z)
		    $ non_alias
		 */;
	}
	else if (equ_to_JPoint_one(point) /*@ where (base) */)
	{
		//result = { 0,0 };
		memset(result, 0, sizeof(AFPoint));
	}

}
