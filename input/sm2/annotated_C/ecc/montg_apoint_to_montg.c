/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_apoint_to_montg. */

#include "../include/ecc.h"
#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */

void montg_to_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * SM2_H_Z + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_h *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_to_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, A) *
      store_fp(result, mont_p(A)) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
 */
;

int montg_apoint_to_montg(const AFPoint* a, AFPoint* result)
/*@ non_alias
    With X Y
    Require
      store_afpoint_fields(a, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      __return == 1 &&
      store_afpoint_fields(a, X, Y) *
      store_mont_afpoint_coords(result, X, Y) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
 */
;

int montg_apoint_to_montg(const AFPoint* a, AFPoint* result)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_afpoint(a, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      __return == 1 &&
      store_afpoint(a, P) *
      store_mont_afpoint(result, P) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop
 */
;

int montg_apoint_to_montg(const AFPoint* a, AFPoint* result)
/*@ non_alias */
{
	const u32* ax = &(a->x);
	const u32* ay = &(a->y);
	u32* rx = &(result->x);
	u32* ry = &(result->y);

	/* Convert x and y from residue domain to Montgomery domain. */
	montg_to_mod_p(ax, rx)
	/*@
	  where (mont_non_alias) A = X_non_alias
	    $ non_alias
	 */;
	montg_to_mod_p(ay, ry)
	/*@
	  where (mont_non_alias) A = Y_non_alias
	    $ non_alias
	 */;

	return 1;
}
