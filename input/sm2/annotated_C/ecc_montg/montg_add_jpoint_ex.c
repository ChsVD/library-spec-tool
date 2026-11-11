/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_add_jpoint_ex. */

#include "../include/ecc.h"

int montg_add_jpoint(const JPoint* a, const JPoint* b, JPoint* r)
/*@ non_alias
    With (P Q : ec_point)
    Require
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a
    With (P Q : ec_point)
    Require
      r == a &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && r == a &&
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
;

void montg_add_jpoint_ex(
    const JPoint* a, const JPoint* b, JPoint* r)
/*@ non_alias
    With (P Q : ec_point)
    Require
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a
    With (P Q : ec_point)
    Require
      r == a &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      r == a &&
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ non_alias */
/*@ r_eq_a */
{
	montg_add_jpoint(a, b, r)
	/*@ where (non_alias) P = P_non_alias, Q = Q_non_alias
	      $ non_alias
	    where (r_eq_a) P = P_r_eq_a, Q = Q_r_eq_a
	      $ r_eq_a */;
}
