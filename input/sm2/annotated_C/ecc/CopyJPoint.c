/* Verification copy of YCrypt/sm2/include/ecc.h::CopyJPoint. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */

JPoint* memcpy(JPoint* dest, const JPoint* src, size_t n)
/*@ non_alias
    With X Y Z
    Require
      n == sizeof(struct JPoint) &&
      store_jpoint_fields(src, X, Y, Z) *
      UInt64Array::undef_full(&(dest->x.v[0]), 4) *
      UInt64Array::undef_full(&(dest->y.v[0]), 4) *
      UInt64Array::undef_full(&(dest->z.v[0]), 4)
    Ensure
      __return == dest &&
      store_jpoint_fields(src, X, Y, Z) *
      store_jpoint_fields(dest, X, Y, Z)
 */
/*@ in_place
    With X Y Z
    Require
      dest == src && n == sizeof(struct JPoint) &&
      store_jpoint_fields(src, X, Y, Z)
    Ensure
      __return == dest && dest == src &&
      store_jpoint_fields(dest, X, Y, Z)
 */
;

inline void CopyJPoint(const JPoint* src, JPoint* dst)
/*@ non_alias
    With X Y Z
    Require
      store_jpoint_fields(src, X, Y, Z) *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure
      store_jpoint_fields(src, X, Y, Z) *
      store_jpoint_fields(dst, X, Y, Z)
 */
/*@ in_place
    With X Y Z
    Require
      dst == src && store_jpoint_fields(src, X, Y, Z)
    Ensure
      dst == src && store_jpoint_fields(dst, X, Y, Z)
 */
;

inline void CopyJPoint(const JPoint* src, JPoint* dst)
/*@ mont_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(src, P) *
      UInt64Array::undef_full(&(dst->x.v[0]), 4) *
      UInt64Array::undef_full(&(dst->y.v[0]), 4) *
      UInt64Array::undef_full(&(dst->z.v[0]), 4)
    Ensure
      store_mont_jpoint(src, P) *
      store_mont_jpoint(dst, P)
 */
;

inline void CopyJPoint(const JPoint* src, JPoint* dst)
/*@ mont_in_place <= in_place
    With (P : ec_point)
    Require
      dst == src && store_mont_jpoint(src, P)
    Ensure
      dst == src && store_mont_jpoint(dst, P)
 */
;

inline void CopyJPoint(const JPoint* src, JPoint* dst)
/*@ non_alias */
/*@ in_place */
{
	memcpy(dst, src, sizeof(JPoint))
	/*@ where (non_alias)
	      X = X_non_alias, Y = Y_non_alias, Z = Z_non_alias
	      $ non_alias
	    where (in_place)
	      X = X_in_place, Y = Y_in_place, Z = Z_in_place
	      $ in_place */;
}
