/*
 * Verification extraction of YCrypt/sm2/ecc_montg.c::montg_set_jpoint_to_zero.
 * Source baseline: be2f5161f972ebc063c7e35b84b129944b754fbc.
 */

#include "../include/ecc_memory.h"
#include "../include/ecc.h"
#include "../include/ecc_constants.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */

// Set jacobian point to zero in montgomery domain
static inline void montg_set_jpoint_to_zero(JPoint* dst)
/*@ coords
    Require
      store_montg_one *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure
      store_montg_one *
      store_mont_jpoint_coords(dst, 1, 1, 0)
 */
;

static inline void montg_set_jpoint_to_zero(JPoint* dst)
/*@ point <= coords
    Require
      store_montg_one *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure
      store_montg_one *
      store_mont_jpoint(dst, ECInfinity)
 */
;

static inline void montg_set_jpoint_to_zero(JPoint* dst)
/*@ coords */
{
	/*@ store_montg_one which implies
	      store_u256_limbs(MONTG_ONE, MONTG_ONE_Z) */
	/*@ do open_store_u256 */
	memcpy(dst->x.v, MONTG_ONE, sizeof(MONTG_ONE));
	memcpy(dst->y.v, MONTG_ONE, sizeof(MONTG_ONE));
	memset(dst->z.v, 0,         sizeof(MONTG_ONE));
}
