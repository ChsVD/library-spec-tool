#include "../include/basicOp.h"

/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

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

u1 u32_add(const u32* a, const u32* b, u32* result)
/*@ non_alias
    With A B
    Require
      store_u256(a, A) *
      store_u256(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        store_u256(a, A) *
        store_u256(b, B) *
        store_u256(result, S)
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        result == a &&
        store_u256(result, S) *
        store_u256(b, B)
 */
;

bool u32_ge(const u32* a, const u32* b)
/*@ With (A B : Z)
    Require
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A >= B) ||
       (__return == 0 && A < B)) &&
      store_u256(a, A) *
      store_u256(b, B)
 */
;

u32* memcpy(u32* dest, UINT64* src, size_t n)
/*@ With X
    Require
      n == 32 &&
      store_u256_limbs(src, X) *
      UInt64Array::undef_full(&(dest->v[0]), 4)
    Ensure
      __return == dest &&
      store_u256_limbs(src, X) *
      store_u256(dest, X)
 */
;

void sm2n_mong_mul_core(UINT64 interim[9], u32* result)
/*@ With T
    Require
      0 <= T && T < SM2_N_Z * U256_MOD &&
      store_u64_limbs(interim, 8, T) *
      store(interim + 8, unsigned long long, 0) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_N_Z &&
        Zout * U256_MOD == T + K * SM2_N_Z &&
        UInt64Array::full_shape(interim, 9) *
		store_fn(result, Zout) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
{
	/*@ do open_store_u64_limbs */
	/*@ do open_sm2_n */
	/*@ do open_sm2_neg_inv_n */
	const size_t LEN = 9;
	int i = 0, j = 0;
	/*@ Inv Assert
	  exists xs K,
	    interim == interim@pre && result == result@pre && LEN == 9 &&
	    0 <= T && T < SM2_N_Z * U256_MOD &&
	    0 <= i && i <= 4 &&
	    0 <= K && K < U64_POW(i) &&
	    Zlength(xs) == 9 &&
	    u64_list_bounded(xs) &&
	    zero_prefix(i, xs) &&
	    0 <= u64_list_value(xs) && u64_list_value(xs) < U576_MOD &&
	    u64_list_value(xs) == T + K * SM2_N_Z &&
	    UInt64Array::full(interim, 9, xs) *
	    UInt64Array::undef_full(&(result->v[0]), 4) *
	    store_sm2_n *
	    store_sm2_rhon *
	    store_sm2_neg_inv_n *
	    has_permission(&j)
	 */
	for (i = 0; i < 4; i++)
	{
		/*@ Given xs K */
		/*@ do open_sm2_n */
		/*@ do open_sm2_neg_inv_n */
		u1 carry = 0;
		u8 h;
		u8 l;
		size_t pos;

		u8 factor = portable_mulx_u64(interim[i], SM2_neg_invN, &h);

		if (factor == 0)
			continue;

		if (factor == 1)
		{
			/*@ Inv Assert
			  exists ys,
			    interim == interim@pre && result == result@pre && LEN == 9 &&
			    0 <= T && T < SM2_N_Z * U256_MOD &&
				    0 <= i && i < 4 && 0 <= j && j <= 4 &&
				    factor == 1 && carry == 0 &&
				    0 <= h && h < U64_MOD &&
				    0 <= K && K < U64_POW(i) &&
			    Zlength(ys) == 9 && u64_list_bounded(ys) &&
			    0 <= u64_list_value(ys) && u64_list_value(ys) < U576_MOD &&
			    ((j == 0 &&
				       Znth(i, ys, 0) * SM2_NEG_INV_N ==
			         factor + h * U64_MOD &&
			       zero_prefix(i, ys) &&
			       u64_list_value(ys) == T + K * SM2_N_Z) ||
			     (j == 1 &&
			       zero_prefix(i + 1, ys) &&
			       u64_list_value(ys) == T + K * SM2_N_Z +
			         SM2_N0_Z * U64_POW(i)) ||
			     (j == 2 &&
			       zero_prefix(i + 1, ys) &&
			       u64_list_value(ys) == T + K * SM2_N_Z +
			         SM2_N0_Z * U64_POW(i) +
			         SM2_N1_Z * U64_POW(i + 1)) ||
			     (j == 3 &&
			       zero_prefix(i + 1, ys) &&
			       u64_list_value(ys) == T + K * SM2_N_Z +
			         SM2_N0_Z * U64_POW(i) +
			         SM2_N1_Z * U64_POW(i + 1) +
			         SM2_N2_Z * U64_POW(i + 2)) ||
			     (j == 4 &&
			       zero_prefix(i + 1, ys) &&
			       u64_list_value(ys) ==
			         T + (K + U64_POW(i)) * SM2_N_Z)) &&
			    UInt64Array::full(interim, 9, ys) *
			    UInt64Array::undef_full(&(result->v[0]), 4) *
			    store_sm2_n * store_sm2_rhon * store_sm2_neg_inv_n *
				    has_permission(&l) * has_permission(&pos)
			 */
			for (j = 0; j < 4; j++)
			{
				/*@ Given ys */
				/*@ do open_sm2_n */
				carry = portable_addcarryx_u64(carry, interim[i + j + 0], SM2_N.v[j], &interim[i + j + 0]);
				pos = 1 + i + j;
				/*@ Inv Assert
				  exists zs V,
				    interim == interim@pre && result == result@pre && LEN == 9 &&
				    0 <= T && T < SM2_N_Z * U256_MOD &&
				    0 <= i && i < 4 && 0 <= j && j < 4 && factor == 1 &&
				    0 <= K && K < U64_POW(i) &&
					    1 + i + j <= pos && pos <= 9 &&
					    0 <= carry && carry <= 1 && pos + carry <= 9 &&
					    0 <= h && h < U64_MOD &&
				    Zlength(zs) == 9 && u64_list_bounded(zs) &&
				    zero_prefix(i + 1, zs) &&
				    0 <= u64_list_value(zs) && u64_list_value(zs) < U576_MOD &&
				    u64_list_value(zs) + carry * U64_POW(pos) == V &&
				    ((j == 0 && V == T + K * SM2_N_Z +
				         SM2_N0_Z * U64_POW(i)) ||
				     (j == 1 && V == T + K * SM2_N_Z +
				         SM2_N0_Z * U64_POW(i) +
				         SM2_N1_Z * U64_POW(i + 1)) ||
				     (j == 2 && V == T + K * SM2_N_Z +
				         SM2_N0_Z * U64_POW(i) +
				         SM2_N1_Z * U64_POW(i + 1) +
				         SM2_N2_Z * U64_POW(i + 2)) ||
				     (j == 3 && V ==
				         T + (K + U64_POW(i)) * SM2_N_Z)) &&
				    UInt64Array::full(interim, 9, zs) *
				    UInt64Array::undef_full(&(result->v[0]), 4) *
				    store_sm2_n * store_sm2_rhon * store_sm2_neg_inv_n *
					    has_permission(&l)
				 */
				while (carry && pos < LEN)
				{
					carry = portable_addcarryx_u64(carry, interim[pos], 0, &interim[pos]);
					++pos;
				}
			}
			continue;
		}

		carry = 0;
		l = portable_mulx_u64(factor, SM2_N.v[0], &h);
		carry = portable_addcarryx_u64(carry, interim[i + 0], l, &interim[i + 0]);
		carry = portable_addcarryx_u64(carry, interim[i + 1], h, &interim[i + 1]);
		pos = 2 + i;
		/*@ Inv Assert
		  exists ys,
		    interim == interim@pre && result == result@pre && LEN == 9 &&
		    0 <= T && T < SM2_N_Z * U256_MOD &&
		    0 <= i && i < 4 &&
		    0 <= factor && factor < U64_MOD && factor != 0 && factor != 1 &&
		    0 <= K && K < U64_POW(i) &&
		    2 + i <= pos && pos <= 9 &&
		    0 <= carry && carry <= 1 && pos + carry <= 9 &&
		    0 <= h && h < U64_MOD && 0 <= l && l < U64_MOD &&
		    Zlength(ys) == 9 && u64_list_bounded(ys) &&
		    zero_prefix(i + 1, ys) &&
		    0 <= u64_list_value(ys) && u64_list_value(ys) < U576_MOD &&
		    0 <= T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW(i) &&
		    T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW(i) < U576_MOD &&
		    u64_list_value(ys) + carry * U64_POW(pos) ==
		      T + K * SM2_N_Z + factor * SM2_N0_Z * U64_POW(i) &&
		    UInt64Array::full(interim, 9, ys) *
		    UInt64Array::undef_full(&(result->v[0]), 4) *
		    store_sm2_n * store_sm2_rhon * store_sm2_neg_inv_n *
		    has_permission(&j)
		 */
		while (carry && pos < LEN)
		{
			carry = portable_addcarryx_u64(carry, interim[pos], 0, &interim[pos]);
			++pos;
		}

		carry = 0;
		h = factor - 1;
		l = ~factor + 1;
		carry = portable_addcarryx_u64(carry, interim[i + 2], l, &interim[i + 2]);
		carry = portable_addcarryx_u64(carry, interim[i + 3], h, &interim[i + 3]);
		pos = 4 + i;
		/*@ Inv Assert
		  exists ys,
		    interim == interim@pre && result == result@pre && LEN == 9 &&
		    0 <= T && T < SM2_N_Z * U256_MOD && 0 <= i && i < 4 &&
		    0 <= factor && factor < U64_MOD && factor != 0 && factor != 1 &&
		    0 <= K && K < U64_POW(i) &&
		    4 + i <= pos && pos <= 9 &&
		    0 <= carry && carry <= 1 && pos + carry <= 9 &&
		    0 <= h && h < U64_MOD && 0 <= l && l < U64_MOD &&
		    Zlength(ys) == 9 && u64_list_bounded(ys) &&
		    zero_prefix(i + 1, ys) &&
		    0 <= u64_list_value(ys) && u64_list_value(ys) < U576_MOD &&
		    0 <= T + K * SM2_N_Z +
		      factor * SM2_N0_Z * U64_POW(i) +
		      factor * SM2_N2_Z * U64_POW(i + 2) &&
		    T + K * SM2_N_Z +
		      factor * SM2_N0_Z * U64_POW(i) +
		      factor * SM2_N2_Z * U64_POW(i + 2) < U576_MOD &&
		    u64_list_value(ys) + carry * U64_POW(pos) ==
		      T + K * SM2_N_Z +
		      factor * SM2_N0_Z * U64_POW(i) +
		      factor * SM2_N2_Z * U64_POW(i + 2) &&
		    UInt64Array::full(interim, 9, ys) *
		    UInt64Array::undef_full(&(result->v[0]), 4) *
		    store_sm2_n * store_sm2_rhon * store_sm2_neg_inv_n *
		    has_permission(&j)
		 */
		while (carry && pos < LEN)
		{
			carry = portable_addcarryx_u64(carry, interim[pos], 0, &interim[pos]);
			++pos;
		}

		/*@ do open_sm2_n */
		carry = 0;
		l = portable_mulx_u64(factor, SM2_N.v[1], &h);
		carry = portable_addcarryx_u64(carry, interim[i + 1], l, &interim[i + 1]);
		carry = portable_addcarryx_u64(carry, interim[i + 2], h, &interim[i + 2]);
		pos = 3 + i;
		/*@ Inv Assert
		  exists ys,
		    interim == interim@pre && result == result@pre && LEN == 9 &&
		    0 <= T && T < SM2_N_Z * U256_MOD && 0 <= i && i < 4 &&
		    0 <= factor && factor < U64_MOD && factor != 0 && factor != 1 &&
		    0 <= K && K < U64_POW(i) &&
		    3 + i <= pos && pos <= 9 &&
		    0 <= carry && carry <= 1 && pos + carry <= 9 &&
		    0 <= h && h < U64_MOD && 0 <= l && l < U64_MOD &&
		    Zlength(ys) == 9 && u64_list_bounded(ys) &&
		    zero_prefix(i + 1, ys) &&
		    0 <= u64_list_value(ys) && u64_list_value(ys) < U576_MOD &&
		    0 <= T + K * SM2_N_Z +
		      factor * SM2_N0_Z * U64_POW(i) +
		      factor * SM2_N2_Z * U64_POW(i + 2) +
		      factor * SM2_N1_Z * U64_POW(i + 1) &&
		    T + K * SM2_N_Z +
		      factor * SM2_N0_Z * U64_POW(i) +
		      factor * SM2_N2_Z * U64_POW(i + 2) +
		      factor * SM2_N1_Z * U64_POW(i + 1) < U576_MOD &&
		    u64_list_value(ys) + carry * U64_POW(pos) ==
		      T + K * SM2_N_Z +
		      factor * SM2_N0_Z * U64_POW(i) +
		      factor * SM2_N2_Z * U64_POW(i + 2) +
		      factor * SM2_N1_Z * U64_POW(i + 1) &&
		    UInt64Array::full(interim, 9, ys) *
		    UInt64Array::undef_full(&(result->v[0]), 4) *
		    store_sm2_n * store_sm2_rhon * store_sm2_neg_inv_n *
		    has_permission(&j)
		 */
		while (carry && pos < LEN)
		{
			carry = portable_addcarryx_u64(carry, interim[pos], 0, &interim[pos]);
			++pos;
		}

		/*@ do open_sm2_n */
		carry = 0;
		l = portable_mulx_u64(factor, SM2_N.v[3], &h);
		carry = portable_addcarryx_u64(carry, interim[i + 3], l, &interim[i + 3]);
		carry = portable_addcarryx_u64(carry, interim[i + 4], h, &interim[i + 4]);
		pos = 5 + i;
		/*@ Inv Assert
		  exists ys,
		    interim == interim@pre && result == result@pre && LEN == 9 &&
		    0 <= T && T < SM2_N_Z * U256_MOD && 0 <= i && i < 4 &&
		    0 <= factor && factor < U64_MOD && factor != 0 && factor != 1 &&
		    0 <= K && K < U64_POW(i) &&
		    5 + i <= pos && pos <= 9 &&
		    0 <= carry && carry <= 1 && pos + carry <= 9 &&
		    0 <= h && h < U64_MOD && 0 <= l && l < U64_MOD &&
		    Zlength(ys) == 9 && u64_list_bounded(ys) &&
		    zero_prefix(i + 1, ys) &&
		    0 <= u64_list_value(ys) && u64_list_value(ys) < U576_MOD &&
		    0 <= T + (K + factor * U64_POW(i)) * SM2_N_Z &&
		    T + (K + factor * U64_POW(i)) * SM2_N_Z < U576_MOD &&
		    u64_list_value(ys) + carry * U64_POW(pos) ==
		      T + (K + factor * U64_POW(i)) * SM2_N_Z &&
		    UInt64Array::full(interim, 9, ys) *
		    UInt64Array::undef_full(&(result->v[0]), 4) *
		    store_sm2_n * store_sm2_rhon * store_sm2_neg_inv_n *
		    has_permission(&j)
		 */
		while (carry && pos < LEN)
		{
			carry = portable_addcarryx_u64(carry, interim[pos], 0, &interim[pos]);
			++pos;
		}
	}
	/*@ Given xs K */
	/*@
	  0 <= T && T < SM2_N_Z * U256_MOD &&
	  0 <= K && K < U256_MOD &&
	  Zlength(xs) == 9 &&
	  u64_list_bounded(xs) &&
	  zero_prefix(4, xs) &&
	  0 <= u64_list_value(xs) && u64_list_value(xs) < U576_MOD &&
	  u64_list_value(xs) == T + K * SM2_N_Z &&
	  UInt64Array::full(interim, 9, xs)
	  which implies
	  exists X C,
	    0 <= X && X < U256_MOD &&
	    0 <= C && C <= 1 &&
	    0 <= X + C * U256_MOD && X + C * U256_MOD < 2 * U256_MOD &&
	    X + C * U256_MOD < U256_MOD + SM2_N_Z &&
	    (X + C * U256_MOD) * U256_MOD == T + K * SM2_N_Z &&
	    UInt64Array::full_shape(interim, 4) *
	    store_u256_limbs(interim + 4, X) *
	    store(interim + 8, unsigned long long, C)
	 */
	/*@ Given X C */

	memcpy(result, interim + 4, 32) /*@ where X = X */;

	/*@ do open_sm2_rhon */
	if (interim[8] != 0)
		u32_add(result, &SM2_rhoN, result) /*@ where (r_eq_a) */;
	/*@ Branch join all with
	  exists Y Xkeep Ckeep,
	    result == result@pre &&
	    0 <= Y && Y < U256_MOD &&
	    Y < 2 * SM2_N_Z &&
	    Y * U256_MOD == T + (K - Ckeep * U256_MOD) * SM2_N_Z &&
	    0 <= Xkeep && Xkeep < U256_MOD &&
	    0 <= Ckeep && Ckeep <= 1 &&
	    0 <= Xkeep + Ckeep * U256_MOD &&
	    Xkeep + Ckeep * U256_MOD < 2 * U256_MOD &&
	    Xkeep + Ckeep * U256_MOD < U256_MOD + SM2_N_Z &&
	    (Xkeep + Ckeep * U256_MOD) * U256_MOD == T + K * SM2_N_Z &&
	    store_u256(result, Y) *
	    UInt64Array::full_shape(interim, 4) *
	    store_u256_limbs(interim + 4, Xkeep) *
	    store(interim + 8, unsigned long long, Ckeep) *
	    store_sm2_n *
	    store_sm2_rhon *
	    store_sm2_neg_inv_n
	 */
	/*@ Given Y Xkeep Ckeep */

	/*@ do open_sm2_n */
	/*@ do open_sm2_rhon */
	if (u32_ge(result, &SM2_N))
		u32_add(result, &SM2_rhoN, result) /*@ where (r_eq_a) */;
	/*@ Branch join all with Assert
	  exists Zout K2,
	    result == result@pre && interim == interim@pre &&
	    0 <= Zout && Zout < SM2_N_Z &&
	    Zout * U256_MOD == T + K2 * SM2_N_Z &&
	    store_u256(result, Zout) *
	    UInt64Array::full_shape(interim, 4) *
	    store_u256_limbs(interim + 4, Xkeep) *
	    store(interim + 8, unsigned long long, Ckeep) *
	    store_sm2_n *
	    store_sm2_rhon *
	    store_sm2_neg_inv_n *
	    has_permission(&j) *
	    has_permission(&i) *
	    has_permission(&LEN)
	 */
	/*@ Given Zout K2 */
}
