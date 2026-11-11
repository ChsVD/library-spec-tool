/*
 * Verification extraction of YCrypt raw_mul.
 *
 * The target function below comes from bignumber/YCrypt/sm2/basicOp.c.
 */

#include "../include/basicOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/raw_mul_arrays.strategies" */

u1 portable_addcarryx_u64(u1 carry_in, u8 a, u8 b, u8* result)
/*@ Require
      0 <= carry_in && carry_in <= 1 &&
      0 <= a && a < U64_MOD &&
      0 <= b && b < U64_MOD &&
      has_permission(result)
    Ensure
      exists out,
        0 <= out && out < U64_MOD &&
        0 <= __return && __return <= 1 &&
        a + b + carry_in == out + __return * U64_MOD &&
        store(result, unsigned long long, out)
 */
;

u8 portable_mulx_u64(u8 a, u8 b, u8* hi_ptr)
/*@ Require
      0 <= a && a < U64_MOD &&
      0 <= b && b < U64_MOD &&
      has_permission(hi_ptr)
    Ensure
      exists hi,
        0 <= __return && __return < U64_MOD &&
        0 <= hi && hi < U64_MOD &&
        a * b == __return + hi * U64_MOD &&
        store(hi_ptr, unsigned long long, hi)
 */
;

void raw_mul(const UINT64 a[4], const UINT64 b[4], UINT64 result[8])
/*@ non_alias
    With A B
    Require
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B) *
      UInt64Array::undef_full(result, 8)
    Ensure
      0 <= A * B && A * B < U512_MOD &&
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B) *
      store_u64_limbs(result, 8, A * B)
 */
/*@ a_eq_b
    With A
    Require
      a == b &&
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(result, 8)
    Ensure
      a == b &&
      0 <= A * A && A * A < U512_MOD &&
      store_u256_limbs(a, A) *
      store_u64_limbs(result, 8, A * A)
 */
/*@ non_alias */
/*@ a_eq_b */
{
	/*@ do open_store_u256 */
	u8 h, l;
	u1 carry, carry2 = 0;
	result[2] = 0;
	result[1] = 0;
	result[0] = 0;

#define MUL_ACC(i, j) \
	l = portable_mulx_u64(a[i], b[j], &h); \
	carry = portable_addcarryx_u64(0, result[(i)+(j)], l, &result[(i)+(j)]); \
	carry2 += portable_addcarryx_u64(carry, result[(i)+(j)+1], h, &result[(i)+(j)+1])

	MUL_ACC(0, 0);

	MUL_ACC(0, 1);
	MUL_ACC(1, 0);
	result[3] = carry2; carry2 = 0;

	MUL_ACC(0, 2);
	MUL_ACC(1, 1);
	MUL_ACC(2, 0);
	result[4] = carry2; carry2 = 0;

	MUL_ACC(0, 3);
	MUL_ACC(1, 2);
	MUL_ACC(2, 1);
	MUL_ACC(3, 0);
	result[5] = carry2; carry2 = 0;
	/*@ Assert
	      exists aa0 aa1 aa2 aa3 ar0 ar1 ar2 ar3 ar4 ar5,
	        a == a@pre && b == b@pre && result == result@pre &&
	        a == b &&
	        0 <= aa0 && aa0 < U64_MOD &&
	        0 <= aa1 && aa1 < U64_MOD &&
	        0 <= aa2 && aa2 < U64_MOD &&
	        0 <= aa3 && aa3 < U64_MOD &&
	        A_a_eq_b == u256_of_limbs(aa0, aa1, aa2, aa3) &&
	        0 <= ar0 && ar0 < U64_MOD &&
	        0 <= ar1 && ar1 < U64_MOD &&
	        0 <= ar2 && ar2 < U64_MOD &&
	        0 <= ar3 && ar3 < U64_MOD &&
	        0 <= ar4 && ar4 < U64_MOD &&
	        0 <= ar5 && ar5 < U64_MOD &&
	        raw_mul_prefix_3(aa0, aa1, aa2, aa3,
	                         aa0, aa1, aa2, aa3) ==
	          ar0 + ar1 * U64_MOD + ar2 * U64_MOD * U64_MOD +
	          ar3 * U64_MOD * U64_MOD * U64_MOD +
	          ar4 * U64_MOD * U64_MOD * U64_MOD * U64_MOD +
	          ar5 * U64_MOD * U64_MOD * U64_MOD * U64_MOD * U64_MOD &&
	        store(a + (0 * sizeof(unsigned long long)), unsigned long long, aa0) *
	        store(a + (1 * sizeof(unsigned long long)), unsigned long long, aa1) *
	        store(a + (2 * sizeof(unsigned long long)), unsigned long long, aa2) *
	        store(a + (3 * sizeof(unsigned long long)), unsigned long long, aa3) *
	        store(result + (0 * sizeof(unsigned long long)), unsigned long long, ar0) *
	        store(result + (1 * sizeof(unsigned long long)), unsigned long long, ar1) *
	        store(result + (2 * sizeof(unsigned long long)), unsigned long long, ar2) *
	        store(result + (3 * sizeof(unsigned long long)), unsigned long long, ar3) *
	        store(result + (4 * sizeof(unsigned long long)), unsigned long long, ar4) *
	        store(result + (5 * sizeof(unsigned long long)), unsigned long long, ar5) *
	        UInt64Array::undef_seg(result, 6, 8) *
	        has_permission(&h) * has_permission(&l) *
	        has_permission(&carry) *
	        store(&carry2, unsigned char, 0)
	        $ a_eq_b
	 */
	/*@ Assert
	      exists na0 na1 na2 na3 nb0 nb1 nb2 nb3
	             nr0 nr1 nr2 nr3 nr4 nr5,
	        a == a@pre && b == b@pre && result == result@pre &&
	        0 <= na0 && na0 < U64_MOD &&
	        0 <= na1 && na1 < U64_MOD &&
	        0 <= na2 && na2 < U64_MOD &&
	        0 <= na3 && na3 < U64_MOD &&
	        0 <= nb0 && nb0 < U64_MOD &&
	        0 <= nb1 && nb1 < U64_MOD &&
	        0 <= nb2 && nb2 < U64_MOD &&
	        0 <= nb3 && nb3 < U64_MOD &&
	        A_non_alias == u256_of_limbs(na0, na1, na2, na3) &&
	        B_non_alias == u256_of_limbs(nb0, nb1, nb2, nb3) &&
	        0 <= nr0 && nr0 < U64_MOD &&
	        0 <= nr1 && nr1 < U64_MOD &&
	        0 <= nr2 && nr2 < U64_MOD &&
	        0 <= nr3 && nr3 < U64_MOD &&
	        0 <= nr4 && nr4 < U64_MOD &&
	        0 <= nr5 && nr5 < U64_MOD &&
	        raw_mul_prefix_3(na0, na1, na2, na3,
	                         nb0, nb1, nb2, nb3) ==
	          nr0 + nr1 * U64_MOD + nr2 * U64_MOD * U64_MOD +
	          nr3 * U64_MOD * U64_MOD * U64_MOD +
	          nr4 * U64_MOD * U64_MOD * U64_MOD * U64_MOD +
	          nr5 * U64_MOD * U64_MOD * U64_MOD * U64_MOD * U64_MOD &&
	        store(a + (0 * sizeof(unsigned long long)), unsigned long long, na0) *
	        store(a + (1 * sizeof(unsigned long long)), unsigned long long, na1) *
	        store(a + (2 * sizeof(unsigned long long)), unsigned long long, na2) *
	        store(a + (3 * sizeof(unsigned long long)), unsigned long long, na3) *
	        store(b + (0 * sizeof(unsigned long long)), unsigned long long, nb0) *
	        store(b + (1 * sizeof(unsigned long long)), unsigned long long, nb1) *
	        store(b + (2 * sizeof(unsigned long long)), unsigned long long, nb2) *
	        store(b + (3 * sizeof(unsigned long long)), unsigned long long, nb3) *
	        store(result + (0 * sizeof(unsigned long long)), unsigned long long, nr0) *
	        store(result + (1 * sizeof(unsigned long long)), unsigned long long, nr1) *
	        store(result + (2 * sizeof(unsigned long long)), unsigned long long, nr2) *
	        store(result + (3 * sizeof(unsigned long long)), unsigned long long, nr3) *
	        store(result + (4 * sizeof(unsigned long long)), unsigned long long, nr4) *
	        store(result + (5 * sizeof(unsigned long long)), unsigned long long, nr5) *
	        UInt64Array::undef_seg(result, 6, 8) *
	        has_permission(&h) * has_permission(&l) *
	        has_permission(&carry) *
	        store(&carry2, unsigned char, 0)
	        $ non_alias
	 */

	MUL_ACC(1, 3);
	MUL_ACC(2, 2);
	MUL_ACC(3, 1);
	result[6] = carry2; carry2 = 0;

	MUL_ACC(2, 3);
	MUL_ACC(3, 2);
	result[7] = carry2;

	MUL_ACC(3, 3);

#undef MUL_ACC
}
